const JS = JuliaSyntax

function _insert_tree_node(graph::SyntaxGraph, k::JS.Kind,
                           src::SourceAttrType, flags::UInt16=0x0000)
    id = newnode!(graph)
    sethead!(graph, id, k)
    setattr!(graph, id, source=src)
    setflags!(graph, id, flags)
    return id
end

"""
An Expr -> SyntaxTree transformation that should preserve semantics, but will
have low-quality provenance info (namely, each tree node will be associated with
the last seen LineNumberNode in the pre-order expr traversal).

Last-resort option so that, for example, we can lower the output of old
Expr-producing macros.  Always prefer re-parsing source text over using this.

Supports parsed and/or macro-expanded exprs, but not lowered exprs
"""
function expr_to_syntaxtree(@nospecialize(e), lnn::Union{LineNumberNode, Nothing}=nothing)
    graph = SyntaxGraph()
    ensure_attributes!(graph,
                       kind=Kind, syntax_flags=UInt16,
                       source=SourceAttrType, var_id=Int, value=Any,
                       name_val=String, is_toplevel_thunk=Bool)
    toplevel_src = if isnothing(lnn)
        # Provenance sinkhole for all nodes until we hit a linenode
        dummy_src = SourceRef(
            SourceFile("No source for expression $e"),
            1, JS.GreenNode(K"None", 0))
        _insert_tree_node(graph, K"None", dummy_src)
    else
        lnn
    end
    st_id, _ = _insert_convert_expr(e, graph, toplevel_src)
    out = SyntaxTree(graph, st_id)
    return out
end

function _expr_replace!(@nospecialize(e), replace_pred::Function, replacer!::Function,
                        recurse_pred=(@nospecialize e)->true)
    if replace_pred(e)
        replacer!(e)
    end
    if e isa Expr && recurse_pred(e)
        for a in e.args
            _expr_replace!(a, replace_pred, replacer!, recurse_pred)
        end
    end
end

function _to_iterspec(exs::Vector)
    if length(exs) === 1 && exs[1].head === :filter
        @assert length(exs[1].args) >= 2
        return Expr(:filter, _to_iterspec(exs[1].args[2:end]), exs[1].args[1])
    end
    outex = Expr(:iteration)
    for e in exs
        if e.head === :block
            for iter in e.args
                push!(outex.args, Expr(:in, iter.args...))
            end
        elseif e.head === :(=)
            push!(outex.args, Expr(:in, e.args...))
        else
            @assert false "unknown iterspec in $e"
        end
    end
    return outex
end

"""
Return `e.args`, but with any parameters in SyntaxTree (flattened, source) order.
Parameters are expected to be as `e.args[pos]`.

e.g. orderings of (a,b,c;d;e;f):
  Expr:       (tuple (parameters (parameters (parameters f) e) d) a b c)
  SyntaxTree: (tuple a b c (parameters d) (parameters e) (parameters f))
"""
function collect_expr_parameters(e::Expr, pos::Int)
    params = expr_parameters(e, pos)
    isnothing(params) && return e.args
    args = Any[e.args[1:pos-1]..., e.args[pos+1:end]...]
    return _flatten_params!(args, params)
end
function _flatten_params!(out::Vector{Any}, p::Expr)
    p1 = expr_parameters(p, 1)
    if !isnothing(p1)
        push!(out, Expr(:parameters, p.args[2:end]...))
        _flatten_params!(out, p1)
    else
        push!(out, p::Any)
    end
    return out
end
function expr_parameters(p::Expr, pos::Int)
    if length(p.args) >= pos &&
        p.args[pos] isa Expr &&
        p.args[pos].head === :parameters
        return p.args[pos]
    end
    return nothing
end

"Unwrap (usually block) if it has only one non-linenode child"
function maybe_strip_block(b::Expr)
    e1 = findfirst(c -> !isa(c, LineNumberNode), b.args)
    isnothing(e1) && return b
    e2 = findfirst(c -> !isa(c, LineNumberNode), b.args[e1+1:end])
    !isnothing(e2) && return b
    return b.args[e1]
end

# Get kind by string if exists.  TODO relies on internals
function find_kind(s::String)
    out = get(JS._kind_str_to_int, s, nothing)
    return isnothing(out) ? nothing : JS.Kind(out)
end

function is_dotted_operator(s::AbstractString)
    return length(s) >= 2 &&
        s[1] === '.' &&
        JS.is_operator(something(find_kind(s[2:end]), K"None"))
end

# Expr doesn't record whether or not var"x" was used on x, so just assume one
# was used for any invalid identifier, but lose the information otherwise.
function _insert_var_str(child::NodeId, graph::SyntaxGraph, src::SourceAttrType)
    var_id = _insert_tree_node(graph, K"var", src)
    setchildren!(graph, var_id, [child])
    setflags!(graph, child, JS.RAW_STRING_FLAG)
    setflags!(graph, var_id, JS.NON_TERMINAL_FLAG)
    return (var_id, src)
end

"""
Insert `e` converted to a syntaxtree into graph and recurse on children.  Return
a pair (my_node_id, last_srcloc).  Should not mutate `e`.

`src` is the latest location found in the pre-order traversal, and is the line
number node to be associated with `e`.
"""
function _insert_convert_expr(@nospecialize(e), graph::SyntaxGraph, src::SourceAttrType)
    if e isa Symbol
        estr = String(e)
        st_k = K"Identifier"
        st_id = _insert_tree_node(graph, st_k, src)
        setattr!(graph, st_id, name_val=estr)
        if !Base.isoperator(e) && !Base.is_valid_identifier(e)
            return _insert_var_str(st_id, graph, src)
        end
        return (st_id, src)
    elseif e isa LineNumberNode
        return (nothing, e)
    # elseif e isa QuoteNode
    #     st_id = _insert_tree_node(graph, K"quote", src)
    #     quote_child, _ = _insert_convert_expr(e.value, graph, src)
    #     setchildren!(graph, st_id, NodeId[quote_child])
    #     return (st_id, src)
    elseif e isa String
        st_id = _insert_tree_node(graph, K"string", src)
        id_inner = _insert_tree_node(graph, K"String", src)
        setattr!(graph, id_inner, value=e)
        setchildren!(graph, st_id, [id_inner])
        return (st_id, src)
    elseif !(e isa Expr)
        if !(e isa Union{Number, Bool, Char, GlobalRef, Nothing})
            @info "unknown leaf type in expr, guessing value:" e typeof(e)
        end
        # TODO: st_k of Float. others?
        st_k = e isa Integer ? K"Integer" : find_kind(string(typeof(e)))
        st_id = _insert_tree_node(graph, isnothing(st_k) ? K"Value" : st_k, src)
        setattr!(graph, st_id, value=e)
        return (st_id, src)
    end
    nargs = length(e.args)

    # `e` is an expr.  In many cases, it suffices to
    # - guess that the kind name is the same as the expr head
    # - add no syntax flags
    # - map e.args to syntax tree children one-to-one
    maybe_kind = find_kind(string(e.head))
    st_k = isnothing(maybe_kind) ? K"None" : maybe_kind
    st_flags = 0x0000
    child_exprs = copy(e.args)

    # The following are special cases where the kind, flags, or children are
    # different from what we guessed above.
    if Base.isoperator(e.head) && st_k === K"None"
        # e.head is an updating assignment operator (+=, .-=, etc).  Non-=
        # dotted ops are wrapped in a call, so we don't reach this.
        s = string(e.head)
        @assert s[end] === '=' && nargs === 2
        if s[1] === '.'
            st_k = K".op="
            op = s[2:end-1]
        else
            st_k = K"op="
            op = s[1:end-1]
        end
        child_exprs = [e.args[1], Symbol(op), e.args[2]]
    elseif e.head === :comparison
        for i = 2:2:length(child_exprs)
            op = child_exprs[i]
            @assert op isa Symbol
            op_s = string(op)
            if is_dotted_operator(op_s)
                child_exprs[i] = Expr(:., Symbol(op_s[2:end]))
            end
        end
    elseif e.head === :macrocall
        @assert nargs >= 2
        a1 = e.args[1]
        child_exprs = collect_expr_parameters(e, 3)
        # macrocall has a linenode "argument" here. should we set src?
        deleteat!(child_exprs, 2)
        if a1 isa Symbol
            child_exprs[1] = Expr(:MacroName, a1)
        elseif a1 isa Expr && a1.head === :(.) && a1.args[2] isa QuoteNode
            child_exprs[1] = Expr(:(.), a1.args[1], Expr(:MacroName, a1.args[2].value))
        elseif a1 isa GlobalRef
            # TODO syntax-introduced macrocalls
            if a1.name === Symbol("@cmd")
                # expr_children = []
            elseif a1.name === Symbol("@doc")
            elseif a1.name === Symbol("@int128_str")
            elseif a1.name === Symbol("@int128_str")
            elseif a1.name === Symbol("@big_str")
            end
        elseif a1 isa Function
        else
            error("Unknown macrocall form $(sprint(dump, e))")
        end

        # TODO node->expr handles do blocks here?
    elseif e.head === :escape || e.head === Symbol("hygienic-scope")
        @assert nargs >= 1
        # Existing behaviour appears to just ignore any extra args
        return _insert_convert_expr(e.args[1], graph, src)
    elseif e.head === :meta
        @assert nargs <= 2
        @assert e.args[1] isa Symbol
        child_exprs[1] = Expr(:sym_not_identifier, e.args[1])
    elseif e.head === Symbol("'")
        @assert nargs === 1
        st_k = K"call"
        st_flags |= JS.POSTFIX_OP_FLAG
        child_exprs = [e.head, e.args[1]]
    elseif e.head === :. && nargs === 2
        a2 = e.args[2]
        if a2 isa Expr && a2.head === :tuple
            st_k = K"dotcall"
            tuple_exprs = collect_expr_parameters(a2, 1)
            child_exprs = pushfirst!(tuple_exprs, e.args[1])
        elseif a2 isa QuoteNode && a2.value isa Symbol
            e.args[2] = a2.value
        elseif a2 isa Expr && a2.head === :MacroName
        else
            @error "Unknown 2-arg dot form?" e
        end
    elseif e.head === :for
        @assert nargs === 2
        child_exprs = Expr[_to_iterspec(Any[e.args[1]]), e.args[2]]
    elseif e.head === :where
        @assert nargs >= 2
        if !(e.args[2] isa Expr && e.args[2].head === :braces)
            child_exprs = [e.args[1], Expr(:braces, e.args[2:end]...)]
        end
    elseif e.head in (:tuple, :vect, :braces)
        child_exprs = collect_expr_parameters(e, 1)
    elseif e.head in (:curly, :ref)
        child_exprs = collect_expr_parameters(e, 2)
    elseif e.head === :try
        child_exprs = Any[e.args[1]]
        # Expr:
        # (try (block ...) var       (block ...) [block ...] [block ...])
        # #     try        catch_var  catch       finally     else
        # SyntaxTree:
        #   (try (block ...)
        #        [catch var (block ...)]
        #        [else (block ...)]
        #        [finally (block ...)])
        if e.args[2] != false || e.args[3] != false
            push!(child_exprs,
                  Expr(:catch,
                       e.args[2] === false ? Expr(:catch_var_placeholder) : e.args[2],
                       e.args[3] === false ? nothing : e.args[3]))
        end
        if nargs >= 5
            push!(child_exprs, Expr(:else, e.args[5]))
        end
        if nargs >= 4
            push!(child_exprs,
                  Expr(:finally, e.args[4] === false ? nothing : e.args[4]))
        end
    elseif e.head === :generator # TODO flatten
        child_exprs = [e.args[1], _to_iterspec(e.args[2:end])]
    elseif e.head === :ncat || e.head === :nrow
        st_flags |= JS.set_numeric_flags(e.args[1])
        child_exprs = child_exprs[2:end]
    elseif e.head === :typed_ncat
        st_flags |= JS.set_numeric_flags(e.args[2])
        deleteat!(child_exprs, 2)
    elseif e.head === :(->)
        @assert nargs === 2
        if e.args[1] isa Symbol
            child_exprs[1] = Expr(:tuple, e.args[1])
        end
        child_exprs[2] = maybe_strip_block(e.args[2])
    elseif e.head === :call
        child_exprs = collect_expr_parameters(e, 2)
        a1 = child_exprs[1]
        if a1 isa Symbol
            a1s = string(a1)
            if is_dotted_operator(a1s)
                # non-assigning dotop like .+ or .==
                st_k = K"dotcall"
                child_exprs[1] = Symbol(a1s[2:end])
            end
        end
    elseif e.head === :(=)
        if e.args[1] isa Expr && e.args[1].head === :call
            st_k = K"function"
            st_flags |= JS.SHORT_FORM_FUNCTION_FLAG
            child_exprs[2] = maybe_strip_block(child_exprs[2])
        end
    elseif e.head === :module
        @assert nargs === 3
        if !e.args[1]
            st_flags |= JS.BARE_MODULE_FLAG
        end
        child_exprs = [e.args[2], e.args[3]]
    elseif e.head === :do
        # Expr:
        # (do (call f args...) (-> (tuple lam_args...) (block ...)))
        # SyntaxTree:
        # (call f args... (do (tuple lam_args...) (block ...)))
        st_k = K"call"
        child_exprs = [e.args[1].args..., Expr(:do_lambda, e.args[2].args...)]
    elseif e.head === :let
        if nargs >= 1 && e.args[1] isa Expr && e.args[1].head !== :block
            child_exprs[1] = Expr(:block, e.args[1])
        end
    elseif e.head === :struct
        e.args[1] && (st_flags |= JS.MUTABLE_FLAG)
        child_exprs = child_exprs[2:end]
        # TODO handle docstrings after refactor
    elseif (e.head === :using || e.head === :import)
        _expr_replace!(e,
                       (e)->(e isa Expr && e.head === :.),
                       (e)->(e.head = :importpath))
    elseif e.head === :kw
        st_k = K"="
    end

    # Temporary heads introduced by converting the parent expr
    if e.head === :MacroName
        @assert nargs === 1
        st_id = _insert_tree_node(graph, K"MacroName", src, st_flags)
        mac_name = string(e.args[1])
        setattr!(graph, st_id, name_val=mac_name == "@__dot__" ? "@." : mac_name)
        if !Base.is_valid_identifier(mac_name[2:end])
            return _insert_var_str(st_id, graph, src)
        end
        return (st_id, src)
    elseif e.head === :catch_var_placeholder
        st_id = _insert_tree_node(graph, K"Placeholder", src, st_flags)
        setattr!(graph, st_id, name_val="")
        return (st_id, src)
    elseif e.head === :sym_not_identifier
        estr = String(e.args[1])
        st_k = K"Symbol"
        st_id = _insert_tree_node(graph, st_k, src)
        setattr!(graph, st_id, name_val=estr)
        return (st_id, src)
    elseif e.head === :do_lambda
        st_k = K"do"
    end

    if st_k === K"None"
        error("no kind for expr head `$(e.head)`\n$(sprint(dump, e))")
    end

    st_flags |= JS.NON_TERMINAL_FLAG
    st_id = _insert_tree_node(graph, st_k, src, st_flags)
    st_child_ids = NodeId[]
    last_src = src
    for c in child_exprs
        (c_id, c_src) = _insert_convert_expr(c, graph, last_src)
        isnothing(c_id) || push!(st_child_ids, c_id)
        last_src = something(c_src, src)
    end

    setchildren!(graph, st_id, st_child_ids)
    return (st_id, last_src)
end
