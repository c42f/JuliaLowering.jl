#-------------------------------------------------------------------------------
# @chk: Basic AST structure checking tool
#
# Check a condition involving an expression, throwing a LoweringError if it
# doesn't evaluate to true. Does some very simple pattern matching to attempt
# to extract the expression variable from the left hand side.
#
# Forms:
# @chk pred(ex)
# @chk pred(ex) msg
# @chk pred(ex) (msg_display_ex, msg)
macro chk(cond, msg=nothing)
    if Meta.isexpr(msg, :tuple)
        ex = msg.args[1]
        msg = msg.args[2]
    else
        ex = cond
        while true
            if ex isa Symbol
                break
            elseif ex.head == :call
                ex = ex.args[2]
            elseif ex.head == :ref
                ex = ex.args[1]
            elseif ex.head == :.
                ex = ex.args[1]
            elseif ex.head in (:(==), :(in), :<, :>)
                ex = ex.args[1]
            else
                error("Can't analyze $cond")
            end
        end
    end
    quote
        ex = $(esc(ex))
        @assert ex isa SyntaxTree
        ok = try
            $(esc(cond))
        catch
            false
        end
        if !ok
            throw(LoweringError(ex, $(isnothing(msg) ? "expected `$cond`" : esc(msg))))
        end
    end
end

#-------------------------------------------------------------------------------
abstract type AbstractLoweringContext end

"""
Unique symbolic identity for a variable, constant, label, or other entity
"""
const IdTag = Int

"""
Metadata about a binding
"""
struct BindingInfo
    name::String
    kind::Symbol              # :local :global :argument :static_parameter
    mod::Union{Nothing,Module} # Set when `kind === :global`
    type::Union{Nothing,SyntaxTree} # Type, for bindings declared like x::T = 10
    is_const::Bool            # Constant, cannot be reassigned
    is_ssa::Bool              # Single assignment, defined before use
    is_always_defined::Bool   # A local that we know has an assignment that dominates all usages (is never undef)
    is_internal::Bool         # True for internal bindings generated by the compiler
    is_ambiguous_local::Bool  # Local, but would be global in soft scope (ie, the REPL)
    is_nospecialize::Bool     # @nospecialize on this argument (only valid for kind == :argument)
end

function BindingInfo(name::AbstractString, kind::Symbol;
                     mod::Union{Nothing,Module} = nothing,
                     type::Union{Nothing,SyntaxTree} = nothing,
                     is_const::Bool = false,
                     is_ssa::Bool = false,
                     is_always_defined::Bool = is_ssa,
                     is_internal::Bool = false,
                     is_ambiguous_local::Bool = false,
                     is_nospecialize::Bool = false)
    BindingInfo(name, kind, mod, type, is_const, is_ssa, is_always_defined,
                is_internal, is_ambiguous_local, is_nospecialize)
end

"""
Metadata about "entities" (variables, constants, etc) in the program. Each
entity is associated to a unique integer id, the BindingId. A binding will be
inferred for each *name* in the user's source program by symbolic analysis of
the source.

However, bindings can also be introduced programmatically during lowering or
macro expansion: the primary key for bindings is the `BindingId` integer, not
a name.
"""
struct Bindings
    info::Vector{BindingInfo}
end

Bindings() = Bindings(Vector{BindingInfo}())

function new_binding(bindings::Bindings, info::BindingInfo)
    push!(bindings.info, info)
    return length(bindings.info)
end

function _binding_id(id::Integer)
    id
end

function _binding_id(ex::SyntaxTree)
    @chk kind(ex) == K"BindingId"
    ex.var_id
end

function update_binding!(bindings::Bindings, x;
        type=nothing, is_const=nothing, is_always_defined=nothing)
    id = _binding_id(x)
    b = lookup_binding(bindings, id)
    bindings.info[id] = BindingInfo(
        b.name,
        b.kind,
        b.mod,
        isnothing(type) ? b.type : type,
        isnothing(is_const) ? b.is_const : is_const,
        b.is_ssa,
        isnothing(is_always_defined) ? b.is_always_defined : is_always_defined,
        b.is_internal,
        b.is_ambiguous_local,
        b.is_nospecialize
    )
end

function lookup_binding(bindings::Bindings, x)
    bindings.info[_binding_id(x)]
end

function lookup_binding(ctx::AbstractLoweringContext, x)
    lookup_binding(ctx.bindings, x)
end

function update_binding!(ctx::AbstractLoweringContext, x; kws...)
    update_binding!(ctx.bindings, x; kws...)
end

const LayerId = Int

function syntax_graph(ctx::AbstractLoweringContext)
    ctx.graph
end

#-------------------------------------------------------------------------------
# AST creation utilities
_node_id(graph::SyntaxGraph, ex::SyntaxTree) = (check_compatible_graph(graph, ex); ex._id)
function _node_id(graph::SyntaxGraph, ex)
    # Fallback to give a comprehensible error message for use with the @ast macro
    error("Attempt to use `$(repr(ex))` of type `$(typeof(ex))` as an AST node. Try annotating with `::K\"your_intended_kind\"?`")
end

_node_ids(graph::SyntaxGraph) = ()
_node_ids(graph::SyntaxGraph, ::Nothing, cs...) = _node_ids(graph, cs...)
_node_ids(graph::SyntaxGraph, c, cs...) = (_node_id(graph, c), _node_ids(graph, cs...)...)
_node_ids(graph::SyntaxGraph, cs::SyntaxList, cs1...) = (_node_ids(graph, cs...)..., _node_ids(graph, cs1...)...)
function _node_ids(graph::SyntaxGraph, cs::SyntaxList)
    check_compatible_graph(graph, cs)
    cs.ids
end

_unpack_srcref(graph, srcref::SyntaxTree) = _node_id(graph, srcref)
_unpack_srcref(graph, srcref::Tuple)      = _node_ids(graph, srcref...)
_unpack_srcref(graph, srcref)             = srcref

function _push_nodeid!(graph::SyntaxGraph, ids::Vector{NodeId}, val)
    push!(ids, _node_id(graph, val))
end
function _push_nodeid!(graph::SyntaxGraph, ids::Vector{NodeId}, val::Nothing)
    nothing
end
function _append_nodeids!(graph::SyntaxGraph, ids::Vector{NodeId}, vals)
    for v in vals
        _push_nodeid!(graph, ids, v)
    end
end
function _append_nodeids!(graph::SyntaxGraph, ids::Vector{NodeId}, vals::SyntaxList)
    check_compatible_graph(graph, vals)
    append!(ids, vals.ids)
end

function makeleaf(graph::SyntaxGraph, srcref, proto; attrs...)
    id = newnode!(graph)
    ex = SyntaxTree(graph, id)
    copy_attrs!(ex, proto, true)
    setattr!(graph, id; source=_unpack_srcref(graph, srcref), attrs...)
    return ex
end

function _makenode(graph::SyntaxGraph, srcref, proto, children; attrs...)
    id = newnode!(graph)
    setchildren!(graph, id, children)
    ex = SyntaxTree(graph, id)
    copy_attrs!(ex, proto, true)
    setattr!(graph, id; source=_unpack_srcref(graph, srcref), attrs...)
    return SyntaxTree(graph, id)
end
function _makenode(ctx, srcref, proto, children; attrs...)
    _makenode(syntax_graph(ctx), srcref, proto, children; attrs...)
end

function makenode(ctx, srcref, proto, children...; attrs...)
    _makenode(ctx, srcref, proto, _node_ids(syntax_graph(ctx), children...); attrs...)
end

function makeleaf(ctx, srcref, proto; kws...)
    makeleaf(syntax_graph(ctx), srcref, proto; kws...)
end

function makeleaf(ctx, srcref, k::Kind, value; kws...)
    graph = syntax_graph(ctx)
    if k == K"Identifier" || k == K"core" || k == K"top" || k == K"Symbol" ||
            k == K"globalref" || k == K"Placeholder"
        makeleaf(graph, srcref, k; name_val=value, kws...)
    elseif k == K"BindingId"
        makeleaf(graph, srcref, k; var_id=value, kws...)
    elseif k == K"label"
        makeleaf(graph, srcref, k; id=value, kws...)
    elseif k == K"symbolic_label"
        makeleaf(graph, srcref, k; name_val=value, kws...)
    else
        val = k == K"Integer" ? convert(Int,     value) :
              k == K"Float"   ? convert(Float64, value) :
              k == K"String"  ? convert(String,  value) :
              k == K"Char"    ? convert(Char,    value) :
              k == K"Value"   ? value                   :
              k == K"Bool"    ? value                   :
              error("Unexpected leaf kind `$k`")
        makeleaf(graph, srcref, k; value=val, kws...)
    end
end

# TODO: Replace this with makeleaf variant?
function mapleaf(ctx, src, kind)
    ex = makeleaf(syntax_graph(ctx), src, kind)
    # TODO: Value coersion might be broken here due to use of `name_val` vs
    # `value` vs ... ?
    copy_attrs!(ex, src)
    ex
end

# Convenience functions to create leaf nodes referring to identifiers within
# the Core and Top modules.
core_ref(ctx, ex, name) = makeleaf(ctx, ex, K"core", name)
svec_type(ctx, ex) = core_ref(ctx, ex, "svec")
nothing_(ctx, ex) = core_ref(ctx, ex, "nothing")

top_ref(ctx, ex, name) = makeleaf(ctx, ex, K"top", name)

# Create a new SSA binding
function ssavar(ctx::AbstractLoweringContext, srcref, name="tmp")
    # TODO: Store this name in only one place? Probably use the provenance chain?
    id = new_binding(ctx.bindings, BindingInfo(name, :local; is_ssa=true, is_internal=true))
    # Create an identifier
    nameref = makeleaf(ctx, srcref, K"Identifier", name_val=name)
    makeleaf(ctx, nameref, K"BindingId", var_id=id)
end

function add_lambda_local!(ctx::AbstractLoweringContext, id)
    # empty - early passes don't need to record lambda locals
end

# Create a new local mutable variable or lambda argument
# (TODO: rename this?)
function new_mutable_var(ctx::AbstractLoweringContext, srcref, name; kind=:local, kws...)
    @assert kind == :local || kind == :argument
    id = new_binding(ctx.bindings, BindingInfo(name, kind; is_internal=true, kws...))
    nameref = makeleaf(ctx, srcref, K"Identifier", name_val=name)
    var = makeleaf(ctx, nameref, K"BindingId", var_id=id)
    add_lambda_local!(ctx, id)
    var
end

function new_global_binding(ctx::AbstractLoweringContext, srcref, name, mod; kws...)
    id = new_binding(ctx.bindings, BindingInfo(name, :global; is_internal=true, mod=mod, kws...))
    nameref = makeleaf(ctx, srcref, K"Identifier", name_val=name)
    makeleaf(ctx, nameref, K"BindingId", var_id=id)
end

function alias_binding(ctx::AbstractLoweringContext, srcref)
    id = new_binding(ctx.bindings, BindingInfo("alias", :alias; is_internal=true))
    makeleaf(ctx, srcref, K"BindingId", var_id=id)
end

# Assign `ex` to an SSA variable.
# Return (variable, assignment_node)
function assign_tmp(ctx::AbstractLoweringContext, ex, name="tmp")
    var = ssavar(ctx, ex, name)
    assign_var = makenode(ctx, ex, K"=", var, ex)
    var, assign_var
end

function emit_assign_tmp(stmts::SyntaxList, ctx, ex, name="tmp")
    var = ssavar(ctx, ex, name)
    push!(stmts, makenode(ctx, ex, K"=", var, ex))
    var
end

#-------------------------------------------------------------------------------
# @ast macro
function _match_srcref(ex)
    if Meta.isexpr(ex, :macrocall) && ex.args[1] == Symbol("@HERE")
        QuoteNode(ex.args[2])
    else
        esc(ex)
    end
end

function _match_kind(f::Function, srcref, ex)
    kws = []
    if Meta.isexpr(ex, :call)
        kind = esc(ex.args[1])
        args = ex.args[2:end]
        if Meta.isexpr(args[1], :parameters)
            kws = map(esc, args[1].args)
            popfirst!(args)
        end
        while length(args) >= 1 && Meta.isexpr(args[end], :kw)
            pushfirst!(kws, esc(pop!(args)))
        end
        if length(args) == 1
            srcref_tmp = gensym("srcref")
            return quote
                $srcref_tmp = $(_match_srcref(args[1]))
                $(f(kind, srcref_tmp, kws))
            end
        elseif length(args) > 1
            error("Unexpected: extra srcref argument in `$ex`?")
        end
    else
        kind = esc(ex)
    end
    f(kind, srcref, kws)
end

function _expand_ast_tree(ctx, srcref, tree)
    if Meta.isexpr(tree, :(::))
        # Leaf node
        _match_kind(srcref, tree.args[2]) do kind, srcref, kws
            :(makeleaf($ctx, $srcref, $kind, $(esc(tree.args[1])), $(kws...)))
        end
    elseif Meta.isexpr(tree, :call) && tree.args[1] === :(=>)
        # Leaf node with copied attributes
        kind = esc(tree.args[3])
        srcref = esc(tree.args[2])
        :(mapleaf($ctx, $srcref, $kind))
    elseif Meta.isexpr(tree, (:vcat, :hcat, :vect))
        # Interior node
        flatargs = []
        for a in tree.args
            if Meta.isexpr(a, :row)
                append!(flatargs, a.args)
            else
                push!(flatargs, a)
            end
        end
        children_ex = :(let child_ids = Vector{NodeId}(), graph = syntax_graph($ctx)
        end)
        child_stmts = children_ex.args[2].args
        for a in flatargs[2:end]
            child = _expand_ast_tree(ctx, srcref, a)
            if Meta.isexpr(child, :(...))
                push!(child_stmts, :(_append_nodeids!(graph, child_ids, $(child.args[1]))))
            else
                push!(child_stmts, :(_push_nodeid!(graph, child_ids, $child)))
            end
        end
        push!(child_stmts, :(child_ids))
        _match_kind(srcref, flatargs[1]) do kind, srcref, kws
            :(_makenode($ctx, $srcref, $kind, $children_ex; $(kws...)))
        end
    elseif Meta.isexpr(tree, :(:=))
        lhs = tree.args[1]
        rhs = _expand_ast_tree(ctx, srcref, tree.args[2])
        ssadef = gensym("ssadef")
        quote
            ($(esc(lhs)), $ssadef) = assign_tmp($ctx, $rhs, $(string(lhs)))
            $ssadef
        end
    elseif Meta.isexpr(tree, :macrocall)
        esc(tree)
    elseif tree isa Expr
        Expr(tree.head, map(a->_expand_ast_tree(ctx, srcref, a), tree.args)...)
    else
        esc(tree)
    end
end

"""
    @ast ctx srcref tree

Syntactic s-expression shorthand for constructing a `SyntaxTree` AST.

* `ctx` - SyntaxGraph context
* `srcref` - Reference to the source code from which this AST was derived.

The `tree` contains syntax of the following forms:
* `[kind child₁ child₂]` - construct an interior node with children
* `value :: kind`        - construct a leaf node
* `ex => kind`           - convert a leaf node to the given `kind`, copying attributes
                           from it and also using `ex` as the source reference.
* `var := ex`            - Set `var=ssavar(...)` and return an assignment node `\$var=ex`.
                           `var` may be used outside `@ast`
* `cond ? ex1 : ex2`     - Conditional; `ex1` and `ex2` will be recursively expanded.
                           `if ... end` and `if ... else ... end` also work with this.

Any `kind` can be replaced with an expression of the form
* `kind(srcref)` - override the source reference for this node and its children
* `kind(attr=val)` - set an additional attribute
* `kind(srcref; attr₁=val₁, attr₂=val₂)` - the general form

In any place `srcref` is used, the special form `@HERE()` can be used to instead
to indicate that the "primary" location of the source is the location where
`@HERE` occurs.


# Examples

```
@ast ctx srcref [
   K"toplevel"
   [K"using"
       [K"importpath"
           "Base"       ::K"Identifier"(src)
       ]
   ]
   [K"function"
       [K"call"
           "eval"       ::K"Identifier"
           "x"          ::K"Identifier"
       ]
       [K"call"
           "eval"       ::K"core"      
           mn           =>K"Identifier"
           "x"          ::K"Identifier"
       ]
   ]
]
```
"""
macro ast(ctx, srcref, tree)
    quote
        ctx = $(esc(ctx))
        srcref = $(_match_srcref(srcref))
        $(_expand_ast_tree(:ctx, :srcref, tree))
    end
end

#-------------------------------------------------------------------------------
# Mapping and copying of AST nodes
function copy_attrs!(dest, src, all=false)
    # TODO: Make this faster?
    for (name, attr) in pairs(src._graph.attributes)
        if (all || (name !== :source && name !== :kind && name !== :syntax_flags)) &&
                haskey(attr, src._id)
            dest_attr = getattr(dest._graph, name, nothing)
            if !isnothing(dest_attr)
                dest_attr[dest._id] = attr[src._id]
            end
        end
    end
end

function copy_attrs!(dest, head::Union{Kind,JuliaSyntax.SyntaxHead}, all=false)
    if all
        sethead!(dest._graph, dest._id, head)
    end
end

function mapchildren(f::Function, ctx, ex::SyntaxTree, do_map_child::Function;
                     extra_attrs...)
    if is_leaf(ex)
        return ex
    end
    orig_children = children(ex)
    cs = isempty(extra_attrs) ? nothing : SyntaxList(ctx)
    for (i,e) in enumerate(orig_children)
        newchild = do_map_child(i) ? f(e) : e
        if isnothing(cs)
            if newchild == e
                continue
            else
                cs = SyntaxList(ctx)
                append!(cs, orig_children[1:i-1])
            end
        end
        push!(cs::SyntaxList, newchild)
    end
    if isnothing(cs)
        # This function should be allocation-free if no children were changed
        # by the mapping and there's no extra_attrs
        return ex
    end
    cs::SyntaxList
    ex2 = makenode(ctx, ex, head(ex), cs)
    copy_attrs!(ex2, ex)
    setattr!(ex2; extra_attrs...)
    return ex2
end

function mapchildren(f::Function, ctx, ex::SyntaxTree, mapped_children::AbstractVector{<:Integer};
                     extra_attrs...)
    j = Ref(firstindex(mapped_children))
    function do_map_child(i)
        ind = j[]
        if ind <= lastindex(mapped_children) && mapped_children[ind] == i
            j[] += 1
            true
        else
            false
        end
    end
    mapchildren(f, ctx, ex, do_map_child; extra_attrs...)
end

function mapchildren(f::Function, ctx, ex::SyntaxTree; extra_attrs...)
    mapchildren(f, ctx, ex, i->true; extra_attrs...)
end


"""
Copy AST `ex` into `ctx`
"""
function copy_ast(ctx, ex)
    # TODO: Do we need to keep a mapping of node IDs to ensure we don't
    # double-copy here in the case when some tree nodes are pointed to by
    # multiple parents? (How much does this actually happen in practice?)
    s = ex.source
    # TODO: Figure out how to use provenance() here?
    srcref = s isa NodeId ? copy_ast(ctx, SyntaxTree(ex._graph, s))            :
             s isa Tuple  ? map(i->copy_ast(ctx, SyntaxTree(ex._graph, i)), s) :
             s
    if !is_leaf(ex)
        cs = SyntaxList(ctx)
        for e in children(ex)
            push!(cs, copy_ast(ctx, e))
        end
        ex2 = makenode(ctx, srcref, ex, cs)
    else
        ex2 = makeleaf(ctx, srcref, ex)
    end
    return ex2
end

#-------------------------------------------------------------------------------
function set_scope_layer(ctx, ex, layer_id, force)
    k = kind(ex)
    scope_layer = force ? layer_id : get(ex, :scope_layer, layer_id)
    if k == K"module" || k == K"toplevel" || k == K"inert"
        makenode(ctx, ex, ex, children(ex);
                 scope_layer=scope_layer)
    elseif k == K"."
        makenode(ctx, ex, ex, set_scope_layer(ctx, ex[1], layer_id, force), ex[2],
                 scope_layer=scope_layer)
    elseif !is_leaf(ex)
        mapchildren(e->set_scope_layer(ctx, e, layer_id, force), ctx, ex;
                    scope_layer=scope_layer)
    else
        makeleaf(ctx, ex, ex;
                 scope_layer=scope_layer)
    end
end

"""
    adopt_scope(ex, ref)

Copy `ex`, adopting the scope layer of `ref`.
"""
function adopt_scope(ex::SyntaxTree, scope_layer::LayerId)
    set_scope_layer(ex, ex, scope_layer, true)
end

function adopt_scope(ex::SyntaxTree, ref::SyntaxTree)
    adopt_scope(ex, ref.scope_layer)
end

function adopt_scope(exs::SyntaxList, ref)
    out = SyntaxList(syntax_graph(exs))
    for e in exs
        push!(out, adopt_scope(e, ref))
    end
    return out
end

# Type for `meta` attribute, to replace `Expr(:meta)`.
# It's unclear how much flexibility we need here - is a dict good, or could we
# just use a struct? Likely this will be sparse. Alternatively we could just
# use individual attributes but those aren't easy to add on an ad-hoc basis in
# the middle of a pass.
const CompileHints = Base.ImmutableDict{Symbol,Any}

function setmeta(ex::SyntaxTree; kws...)
    @assert length(kws) == 1 # todo relax later ?
    key = first(keys(kws))
    value = first(values(kws))
    meta = begin
        m = get(ex, :meta, nothing)
        isnothing(m) ? CompileHints(key, value) : CompileHints(m, key, value)
    end
    setattr(ex; meta=meta)
end

function getmeta(ex::SyntaxTree, name::Symbol, default)
    meta = get(ex, :meta, nothing)
    isnothing(meta) ? default : get(meta, name, default)
end

#-------------------------------------------------------------------------------
# Predicates and accessors working on expression trees

function is_quoted(ex)
    kind(ex) in KSet"Symbol quote top core globalref break inert
                     meta inbounds inline noinline loopinfo"
end

function extension_type(ex)
    @assert kind(ex) == K"extension" || kind(ex) == K"assert"
    @chk numchildren(ex) >= 1
    @chk kind(ex[1]) == K"Symbol"
    ex[1].name_val
end

function is_sym_decl(x)
    k = kind(x)
    k == K"Identifier" || k == K"::"
end

function is_identifier(x)
    k = kind(x)
    k == K"Identifier" || k == K"var" || is_operator(k) || is_macro_name(k)
end

function is_eventually_call(ex::SyntaxTree)
    k = kind(ex)
    return k == K"call" || ((k == K"where" || k == K"::") && is_eventually_call(ex[1]))
end

function is_function_def(ex)
    k = kind(ex)
    return k == K"function" || k == K"->"
end

function has_parameters(ex::SyntaxTree)
    numchildren(ex) >= 1 && kind(ex[end]) == K"parameters"
end

function has_parameters(args::AbstractVector)
    length(args) >= 1 && kind(args[end]) == K"parameters"
end

function any_assignment(exs)
    any(kind(e) == K"=" for e in exs)
end

# Check valid identifier/function names
function is_valid_name(ex)
    k = kind(ex)
    if k == K"Identifier"
        name = ex.name_val
    elseif k == K"var"
        name = ex[1].name_val
    elseif k == K"." && kind(ex[2]) == K"Symbol"
        name = ex[2].name_val
    else
        return false
    end
    return name != "ccall" && name != "cglobal"
end

function is_valid_modref(ex)
    return kind(ex) == K"." && kind(ex[2]) == K"Symbol" &&
           (kind(ex[1]) == K"Identifier" || is_valid_modref(ex[1]))
end

function decl_var(ex)
    kind(ex) == K"::" ? ex[1] : ex
end

# Remove empty parameters block, eg, in the arg list of `f(x, y;)`
function remove_empty_parameters(args)
    i = length(args)
    while i > 0 && kind(args[i]) == K"parameters" && numchildren(args[i]) == 0
        i -= 1
    end
    args[1:i]
end

function to_symbol(ctx, ex)
    @ast ctx ex ex=>K"Symbol"
end

function new_scope_layer(ctx, mod_ref::Module=ctx.mod)
    new_layer = ScopeLayer(length(ctx.scope_layers)+1, ctx.mod, true)
    push!(ctx.scope_layers, new_layer)
    new_layer.id
end

function new_scope_layer(ctx, mod_ref::SyntaxTree)
    @assert kind(mod_ref) == K"Identifier"
    new_scope_layer(ctx, ctx.scope_layers[mod_ref.scope_layer].mod)
end
