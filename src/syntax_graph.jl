const NodeId = Int

"""
Directed graph with arbitrary attributes on nodes. Used here for representing
one or several syntax trees.

TODO: Global attributes!
"""
mutable struct SyntaxGraph{Attrs}
    edge_ranges::Vector{UnitRange{Int}}
    edges::Vector{NodeId}
    attributes::Attrs
end

SyntaxGraph() = SyntaxGraph{Dict{Symbol,Any}}(Vector{UnitRange{Int}}(),
                                              Vector{NodeId}(), Dict{Symbol,Any}())

# "Freeze" attribute names and types, encoding them in the type of the returned
# SyntaxGraph.
function freeze_attrs(graph::SyntaxGraph)
    frozen_attrs = (; pairs(graph.attributes)...)
    SyntaxGraph(graph.edge_ranges, graph.edges, frozen_attrs)
end

# Create a copy of `graph` where the attribute list is mutable
function unfreeze_attrs(graph::SyntaxGraph)
    unfrozen_attrs = Dict{Symbol,Any}(pairs(graph.attributes)...)
    SyntaxGraph(graph.edge_ranges, graph.edges, unfrozen_attrs)
end

function _show_attrs(io, attributes::Dict)
    show(io, MIME("text/plain"), attributes)
end
function _show_attrs(io, attributes::NamedTuple)
    show(io, MIME("text/plain"), Dict(pairs(attributes)...))
end

function attrnames(graph::SyntaxGraph)
    keys(graph.attributes)
end

function attrdefs(graph::SyntaxGraph)
    [(k=>typeof(v).parameters[2]) for (k, v) in pairs(graph.attributes)]
end

function Base.show(io::IO, ::MIME"text/plain", graph::SyntaxGraph)
    print(io, typeof(graph),
          " with $(length(graph.edge_ranges)) vertices, $(length(graph.edges)) edges, and attributes:\n")
    _show_attrs(io, graph.attributes)
end

function ensure_attributes!(graph::SyntaxGraph; kws...)
    for (k,v) in pairs(kws)
        @assert k isa Symbol
        @assert v isa Type
        if haskey(graph.attributes, k)
            v0 = valtype(graph.attributes[k])
            v == v0 || throw(ErrorException("Attribute type mismatch $v != $v0"))
        elseif graph.attributes isa NamedTuple
            throw(ErrorException("""
                ensure_attributes!: $k is not an existing attribute, and the graph's attributes are frozen. \
                Consider calling non-mutating `ensure_attributes` instead."""))
        else
            graph.attributes[k] = Dict{NodeId,v}()
        end
    end
    graph
end

function ensure_attributes(graph::SyntaxGraph{<:Dict}; kws...)
    g = unfreeze_attrs(graph)
    ensure_attributes!(g; kws...)
end

function ensure_attributes(graph::SyntaxGraph{<:NamedTuple}; kws...)
    g = unfreeze_attrs(graph)
    ensure_attributes!(g; kws...)
    freeze_attrs(g)
end

function delete_attributes!(graph::SyntaxGraph{<:Dict}, attr_names::Symbol...)
    for name in attr_names
        delete!(graph.attributes, name)
    end
    graph
end

function delete_attributes(graph::SyntaxGraph{<:Dict}, attr_names::Symbol...)
    delete_attributes!(unfreeze_attrs(graph), attr_names...)
end

function delete_attributes(graph::SyntaxGraph{<:NamedTuple}, attr_names::Symbol...)
    g = delete_attributes!(unfreeze_attrs(graph), attr_names...)
    freeze_attrs(g)
end

function newnode!(graph::SyntaxGraph)
    push!(graph.edge_ranges, 0:-1) # Invalid range start => leaf node
    return length(graph.edge_ranges)
end

function setchildren!(graph::SyntaxGraph, id, children::NodeId...)
    setchildren!(graph, id, children)
end

function setchildren!(graph::SyntaxGraph, id, children)
    n = length(graph.edges)
    graph.edge_ranges[id] = n+1:(n+length(children))
    # TODO: Reuse existing edges if possible
    append!(graph.edges, children)
end

function JuliaSyntax.is_leaf(graph::SyntaxGraph, id)
    first(graph.edge_ranges[id]) == 0
end

function JuliaSyntax.numchildren(graph::SyntaxGraph, id)
    length(graph.edge_ranges[id])
end

function JuliaSyntax.children(graph::SyntaxGraph, id)
    @view graph.edges[graph.edge_ranges[id]]
end

function JuliaSyntax.children(graph::SyntaxGraph, id, r::UnitRange)
    @view graph.edges[graph.edge_ranges[id][r]]
end

function child(graph::SyntaxGraph, id::NodeId, i::Integer)
    graph.edges[graph.edge_ranges[id][i]]
end

function getattr(graph::SyntaxGraph{<:Dict}, name::Symbol)
    getfield(graph, :attributes)[name]
end

function getattr(graph::SyntaxGraph{<:NamedTuple}, name::Symbol)
    getfield(getfield(graph, :attributes), name)
end

function getattr(graph::SyntaxGraph, name::Symbol, default)
    get(getfield(graph, :attributes), name, default)
end

function hasattr(graph::SyntaxGraph, name::Symbol)
    getattr(graph, name, nothing) !== nothing
end

# TODO: Probably terribly non-inferable?
function setattr!(graph::SyntaxGraph, id; attrs...)
    for (k,v) in pairs(attrs)
        if !isnothing(v)
            getattr(graph, k)[id] = v
        end
    end
end

function Base.getproperty(graph::SyntaxGraph, name::Symbol)
    # TODO: Remove access to internals?
    name === :edge_ranges && return getfield(graph, :edge_ranges)
    name === :edges       && return getfield(graph, :edges)
    name === :attributes  && return getfield(graph, :attributes)
    return getattr(graph, name)
end

function sethead!(graph, id::NodeId, h::JuliaSyntax.SyntaxHead)
    sethead!(graph, id, kind(h))
    setflags!(graph, id, flags(h))
end

function sethead!(graph, id::NodeId, k::Kind)
    graph.kind[id] = k
end

function setflags!(graph, id::NodeId, f::UInt16)
    graph.syntax_flags[id] = f
end

function _convert_nodes(graph::SyntaxGraph, node::SyntaxNode)
    id = newnode!(graph)
    sethead!(graph, id, head(node))
    if !isnothing(node.val)
        v = node.val
        if v isa Symbol
            # TODO: Fixes in JuliaSyntax to avoid ever converting to Symbol
            setattr!(graph, id, name_val=string(v))
        else
            setattr!(graph, id, value=v)
        end
    end
    setattr!(graph, id, source=SourceRef(node.source, node.position, node.raw))
    if !is_leaf(node)
        cs = map(children(node)) do n
            _convert_nodes(graph, n)
        end
        setchildren!(graph, id, cs)
    end
    return id
end

"""
    syntax_graph(ctx)

Return `SyntaxGraph` associated with `ctx`
"""
syntax_graph(graph::SyntaxGraph) = graph

function check_same_graph(x, y)
    if syntax_graph(x) !== syntax_graph(y)
        error("Mismatching syntax graphs")
    end
end

function check_compatible_graph(x, y)
    if !is_compatible_graph(x, y)
        error("Incompatible syntax graphs")
    end
end

function is_compatible_graph(x, y)
    syntax_graph(x).edges === syntax_graph(y).edges
end

#-------------------------------------------------------------------------------
struct SyntaxTree{GraphType}
    _graph::GraphType
    _id::NodeId
end

function Base.getproperty(ex::SyntaxTree, name::Symbol)
    name === :_graph && return getfield(ex, :_graph)
    name === :_id  && return getfield(ex, :_id)
    _id = getfield(ex, :_id)
    return get(getproperty(getfield(ex, :_graph), name), _id) do
        attrstr = join(["\n    $n = $(getproperty(ex, n))"
                        for n in attrnames(ex)], ",")
        error("Property `$name[$_id]` not found. Available attributes:$attrstr")
    end
end

function Base.setproperty!(ex::SyntaxTree, name::Symbol, val)
    return setattr!(ex._graph, ex._id; name=>val)
end

function Base.propertynames(ex::SyntaxTree)
    attrnames(ex)
end

function Base.get(ex::SyntaxTree, name::Symbol, default)
    attr = getattr(getfield(ex, :_graph), name, nothing)
    return isnothing(attr) ? default :
           get(attr, getfield(ex, :_id), default)
end

function Base.getindex(ex::SyntaxTree, i::Integer)
    SyntaxTree(ex._graph, child(ex._graph, ex._id, i))
end

function Base.getindex(ex::SyntaxTree, r::UnitRange)
    SyntaxList(ex._graph, children(ex._graph, ex._id, r))
end

Base.firstindex(ex::SyntaxTree) = 1
Base.lastindex(ex::SyntaxTree) = numchildren(ex)

function hasattr(ex::SyntaxTree, name::Symbol)
    attr = getattr(ex._graph, name, nothing)
    return !isnothing(attr) && haskey(attr, ex._id)
end

function attrnames(ex::SyntaxTree)
    attrs = ex._graph.attributes
    [name for (name, value) in pairs(attrs) if haskey(value, ex._id)]
end

function copy_node(ex::SyntaxTree)
    graph = syntax_graph(ex)
    id = newnode!(graph)
    if !is_leaf(ex)
        setchildren!(graph, id, _node_ids(graph, children(ex)...))
    end
    ex2 = SyntaxTree(graph, id)
    copy_attrs!(ex2, ex, true)
    ex2
end

function setattr(ex::SyntaxTree; extra_attrs...)
    ex2 = copy_node(ex)
    setattr!(ex2; extra_attrs...)
    ex2
end

function setattr!(ex::SyntaxTree; attrs...)
    setattr!(ex._graph, ex._id; attrs...)
end

# JuliaSyntax tree API

function JuliaSyntax.is_leaf(ex::SyntaxTree)
    is_leaf(ex._graph, ex._id)
end

function JuliaSyntax.numchildren(ex::SyntaxTree)
    numchildren(ex._graph, ex._id)
end

function JuliaSyntax.children(ex::SyntaxTree)
    SyntaxList(ex._graph, children(ex._graph, ex._id))
end

function JuliaSyntax.head(ex::SyntaxTree)
    JuliaSyntax.SyntaxHead(kind(ex), flags(ex))
end

function JuliaSyntax.kind(ex::SyntaxTree)
    ex.kind
end

function JuliaSyntax.flags(ex::SyntaxTree)
    get(ex, :syntax_flags, 0x0000)
end


# Reference to bytes within a source file
struct SourceRef
    file::SourceFile
    first_byte::Int
    # TODO: Do we need the green node, or would last_byte suffice?
    green_tree::JuliaSyntax.GreenNode
end

JuliaSyntax.sourcefile(src::SourceRef) = src.file
JuliaSyntax.byte_range(src::SourceRef) = src.first_byte:(src.first_byte + span(src.green_tree) - 1)

# TODO: Adding these methods to support LineNumberNode is kind of hacky but we
# can remove these after JuliaLowering becomes self-bootstrapping for macros
# and we a proper SourceRef for @ast's @HERE form.
JuliaSyntax.byte_range(src::LineNumberNode) = 0:0
JuliaSyntax.source_location(src::LineNumberNode) = (src.line, 0)
JuliaSyntax.source_location(::Type{LineNumberNode}, src::LineNumberNode) = src
JuliaSyntax.source_line(src::LineNumberNode) = src.line
# The follow somewhat strange cases are for where LineNumberNode is standing in
# for SourceFile because we've only got Expr-based provenance info
JuliaSyntax.sourcefile(src::LineNumberNode) = src
JuliaSyntax.sourcetext(src::LineNumberNode) = SubString("")
JuliaSyntax.source_location(src::LineNumberNode, byte_index::Integer) = (src.line, 0)
JuliaSyntax.source_location(::Type{LineNumberNode}, src::LineNumberNode, byte_index::Integer) = src
JuliaSyntax.filename(src::LineNumberNode) = string(src.file)

function JuliaSyntax.highlight(io::IO, src::LineNumberNode; note="")
    print(io, src, " - ", note)
end

function JuliaSyntax.highlight(io::IO, src::SourceRef; kws...)
    highlight(io, src.file, first_byte(src):last_byte(src); kws...)
end

function Base.show(io::IO, ::MIME"text/plain", src::SourceRef)
    highlight(io, src; note="these are the bytes you're looking for 😊", context_lines_inner=20)
end


function provenance(ex::SyntaxTree)
    s = ex.source
    if s isa NodeId
        return (SyntaxTree(ex._graph, s),)
    elseif s isa Tuple
        return SyntaxTree.((ex._graph,), s)
    else
        return (s,)
    end
end


function _sourceref(sources, id)
    i = 1
    while true
        i += 1
        s = sources[id]
        if s isa NodeId
            id = s
        else
            return s, id
        end
    end
end

function sourceref(ex::SyntaxTree)
    sources = ex._graph.source
    id::NodeId = ex._id
    while true
        s, _ = _sourceref(sources, id)
        if s isa Tuple
            s = s[1]
        end
        if s isa NodeId
            id = s
        else
            return s
        end
    end
end

function _flattened_provenance(refs, graph, sources, id)
    # TODO: Implement in terms of `provenance()`?
    s, id2 = _sourceref(sources, id)
    if s isa Tuple
        for i in s
            _flattened_provenance(refs, graph, sources, i)
        end
    else
        push!(refs, SyntaxTree(graph, id2))
    end
end

function flattened_provenance(ex::SyntaxTree)
    refs = SyntaxList(ex)
    _flattened_provenance(refs, ex._graph, ex._graph.source, ex._id)
    return reverse(refs)
end


function is_ancestor(ex, ancestor)
    if !is_compatible_graph(ex, ancestor)
        return false
    end
    sources = ex._graph.source
    id::NodeId = ex._id
    while true
        s = get(sources, id, nothing)
        if s isa NodeId
            id = s
            if id == ancestor._id
                return true
            end
        else
            return false
        end
    end
end

const SourceAttrType = Union{SourceRef,LineNumberNode,NodeId,Tuple}

function SyntaxTree(graph::SyntaxGraph, node::SyntaxNode)
    ensure_attributes!(graph, kind=Kind, syntax_flags=UInt16, source=SourceAttrType,
                       value=Any, name_val=String)
    id = _convert_nodes(graph, node)
    return SyntaxTree(graph, id)
end

function SyntaxTree(node::SyntaxNode)
    return SyntaxTree(SyntaxGraph(), node)
end

attrsummary(name, value) = string(name)
attrsummary(name, value::Number) = "$name=$value"

function _value_string(ex)
    k = kind(ex)
    str = k in KSet"Identifier StrMacroName CmdMacroName" || is_operator(k) ? ex.name_val :
          k == K"Placeholder" ? ex.name_val           :
          k == K"SSAValue"    ? "%"                   :
          k == K"BindingId"   ? "#"                   :
          k == K"label"       ? "label"               :
          k == K"core"        ? "core.$(ex.name_val)" :
          k == K"top"         ? "top.$(ex.name_val)"  :
          k == K"Symbol"      ? ":$(ex.name_val)" :
          k == K"globalref"   ? "$(ex.mod).$(ex.name_val)" :
          k == K"slot"        ? "slot" :
          k == K"latestworld" ? "latestworld" :
          k == K"static_parameter" ? "static_parameter" :
          k == K"symbolic_label" ? "label:$(ex.name_val)" :
          k == K"symbolic_goto" ? "goto:$(ex.name_val)" :
          k == K"SourceLocation" ? "SourceLocation:$(JuliaSyntax.filename(ex)):$(join(source_location(ex), ':'))" :
          repr(get(ex, :value, nothing))
    id = get(ex, :var_id, nothing)
    if isnothing(id)
        id = get(ex, :id, nothing)
    end
    if !isnothing(id)
        idstr = subscript_str(id)
        str = "$(str)$idstr"
    end
    if k == K"slot" || k == K"BindingId"
        p = provenance(ex)[1]
        while p isa SyntaxTree
            if kind(p) == K"Identifier"
                str = "$(str)/$(p.name_val)"
                break
            end
            p = provenance(p)[1]
        end
    end
    return str
end

function _show_syntax_tree(io, ex, indent, show_kinds)
    val = get(ex, :value, nothing)
    nodestr = !is_leaf(ex) ? "[$(untokenize(head(ex)))]" : _value_string(ex)

    treestr = rpad(string(indent, nodestr), 40)
    if show_kinds && is_leaf(ex)
        treestr = treestr*" :: "*string(kind(ex))
    end

    std_attrs = Set([:name_val,:value,:kind,:syntax_flags,:source,:var_id])
    attrstr = join([attrsummary(n, getproperty(ex, n))
                    for n in attrnames(ex) if n ∉ std_attrs], ",")
    treestr = string(rpad(treestr, 60), " │ $attrstr")

    println(io, treestr)
    if !is_leaf(ex)
        new_indent = indent*"  "
        for n in children(ex)
            _show_syntax_tree(io, n, new_indent, show_kinds)
        end
    end
end

function Base.show(io::IO, ::MIME"text/plain", ex::SyntaxTree, show_kinds=true)
    anames = join(string.(attrnames(syntax_graph(ex))), ",")
    println(io, "SyntaxTree with attributes $anames")
    _show_syntax_tree(io, ex, "", show_kinds)
end

function _show_syntax_tree_sexpr(io, ex)
    if is_leaf(ex)
        if is_error(ex)
            print(io, "(", untokenize(head(ex)), ")")
        else
            print(io, _value_string(ex))
        end
    else
        print(io, "(", untokenize(head(ex)))
        first = true
        for n in children(ex)
            print(io, ' ')
            _show_syntax_tree_sexpr(io, n)
            first = false
        end
        print(io, ')')
    end
end

function Base.show(io::IO, ::MIME"text/x.sexpression", node::SyntaxTree)
    _show_syntax_tree_sexpr(io, node)
end

function Base.show(io::IO, node::SyntaxTree)
    _show_syntax_tree_sexpr(io, node)
end

function reparent(ctx, ex::SyntaxTree)
    # Ensure `ex` has the same parent graph, in a somewhat loose sense.
    # Could relax by copying if necessary?
    # In that case, would we copy all the attributes? That would have slightly
    # different semantics.
    graph = syntax_graph(ctx)
    @assert graph.edge_ranges === ex._graph.edge_ranges
    SyntaxTree(graph, ex._id)
end

function ensure_attributes(ex::SyntaxTree; kws...)
    reparent(ensure_attributes(syntax_graph(ex); kws...), ex)
end

syntax_graph(ex::SyntaxTree) = ex._graph

function JuliaSyntax.build_tree(::Type{SyntaxTree}, stream::JuliaSyntax.ParseStream; kws...)
    SyntaxTree(JuliaSyntax.build_tree(SyntaxNode, stream; kws...))
end

JuliaSyntax.sourcefile(ex::SyntaxTree) = sourcefile(sourceref(ex))
JuliaSyntax.byte_range(ex::SyntaxTree) = byte_range(sourceref(ex))

function JuliaSyntax._expr_leaf_val(ex::SyntaxTree, _...)
    name = get(ex, :name_val, nothing)
    if !isnothing(name)
        n = Symbol(name)
        if kind(ex) === K"Symbol"
            return QuoteNode(n)
        elseif hasattr(ex, :scope_layer)
            Expr(:scope_layer, n, ex.scope_layer)
        else
            n
        end
    else
        val = get(ex, :value, nothing)
        if kind(ex) == K"Value" && val isa Expr || val isa LineNumberNode
            # Expr AST embedded in a SyntaxTree should be quoted rather than
            # becoming part of the output AST.
            QuoteNode(val)
        else
            val
        end
    end
end

Base.Expr(ex::SyntaxTree) = JuliaSyntax.to_expr(ex)

#--------------------------------------------------
function _find_SyntaxTree_macro(ex, line)
    @assert !is_leaf(ex)
    for c in children(ex)
        rng = byte_range(c)
        firstline = JuliaSyntax.source_line(sourcefile(c), first(rng))
        lastline = JuliaSyntax.source_line(sourcefile(c), last(rng))
        if line < firstline || lastline < line
            continue
        end
        # We're in the line range. Either
        if firstline == line && kind(c) == K"macrocall" && begin
                    name = c[1]
                    if kind(name) == K"macro_name"
                        name = name[1]
                    end
                    if kind(name) == K"."
                        name = name[2]
                        if kind(name) == K"macro_name"
                            name = name[1]
                        end
                    end
                    @assert kind(name) == K"Identifier"
                    name.name_val == "SyntaxTree"
                end
            # We find the node we're looking for. NB: Currently assuming a max
            # of one @SyntaxTree invocation per line. Though we could relax
            # this with more heuristic matching of the Expr-AST...
            @assert numchildren(c) == 2
            return c[2]
        elseif !is_leaf(c)
            # Recurse
            ex1 = _find_SyntaxTree_macro(c, line)
            if !isnothing(ex1)
                return ex1
            end
        end
    end
    return nothing # Will get here if multiple children are on the same line.
end

# Translate JuliaLowering hygiene to esc() for use in @SyntaxTree
function _scope_layer_1_to_esc!(ex)
    if ex isa Expr
        if ex.head == :scope_layer
            @assert ex.args[2] === 1
            return esc(_scope_layer_1_to_esc!(ex.args[1]))
        else
            map!(_scope_layer_1_to_esc!, ex.args, ex.args)
            return ex
        end
    else
        return ex
    end
end

"""
Macro to construct quoted SyntaxTree literals (instead of quoted Expr literals)
in normal Julia source code.

Example:

```julia
tree1 = @SyntaxTree :(some_unique_identifier)
tree2 = @SyntaxTree quote
    x = 1
    \$tree1 = x
end
```
"""
macro SyntaxTree(ex_old)
    # The implementation here is hilarious and arguably very janky: we
    # 1. Briefly check but throw away the Expr-AST
    if !(Meta.isexpr(ex_old, :quote) || ex_old isa QuoteNode)
        throw(ArgumentError("@SyntaxTree expects a `quote` block or `:`-quoted expression"))
    end
    # 2. Re-parse the current source file as SyntaxTree instead
    fname = isnothing(__source__.file) ? error("No current file") : String(__source__.file)
    if occursin(r"REPL\[\d+\]", fname)
        # Assume we should look at last history entry in REPL
        try
            # Wow digging in like this is an awful hack but `@SyntaxTree` is
            # already a hack so let's go for it I guess 😆
            text = Base.active_repl.mistate.interface.modes[1].hist.history[end]
            if !occursin("@SyntaxTree", text)
                error("Text not found in last REPL history line")
            end
        catch
            error("Text not found in REPL history")
        end
    else
        text = read(fname, String)
    end
    full_ex = parseall(SyntaxTree, text)
    # 3. Using the current file and line number, dig into the re-parsed tree and
    # discover the piece of AST which should be returned.
    ex = _find_SyntaxTree_macro(full_ex, __source__.line)
    # 4. Do the first step of JuliaLowering's syntax lowering to get
    # syntax interpolations to work
    _, ex1 = expand_forms_1(__module__, ex, false, Base.tls_world_age())
    @assert kind(ex1) == K"call" && ex1[1].value == interpolate_ast
    Expr(:call, :interpolate_ast, SyntaxTree, ex1[3][1],
         map(e->_scope_layer_1_to_esc!(Expr(e)), ex1[4:end])...)
end

#-------------------------------------------------------------------------------
# Lightweight vector of nodes ids with associated pointer to graph stored separately.
mutable struct SyntaxList{GraphType, NodeIdVecType} <: AbstractVector{SyntaxTree}
    graph::GraphType
    ids::NodeIdVecType
end

function SyntaxList(graph::SyntaxGraph, ids::AbstractVector{NodeId})
    SyntaxList{typeof(graph), typeof(ids)}(graph, ids)
end

SyntaxList(graph::SyntaxGraph) = SyntaxList(graph, Vector{NodeId}())
SyntaxList(ctx) = SyntaxList(syntax_graph(ctx))

syntax_graph(lst::SyntaxList) = lst.graph

Base.size(v::SyntaxList) = size(v.ids)

Base.IndexStyle(::Type{<:SyntaxList}) = IndexLinear()

Base.getindex(v::SyntaxList, i::Int) = SyntaxTree(v.graph, v.ids[i])

function Base.getindex(v::SyntaxList, r::UnitRange)
    SyntaxList(v.graph, view(v.ids, r))
end

function Base.setindex!(v::SyntaxList, ex::SyntaxTree, i::Int)
    check_compatible_graph(v, ex)
    v.ids[i] = ex._id
end

function Base.setindex!(v::SyntaxList, id::NodeId, i::Int)
    v.ids[i] = id
end

function Base.push!(v::SyntaxList, ex::SyntaxTree)
    check_compatible_graph(v, ex)
    push!(v.ids, ex._id)
end

function Base.pushfirst!(v::SyntaxList, ex::SyntaxTree)
    check_compatible_graph(v, ex)
    pushfirst!(v.ids, ex._id)
end

function Base.similar(v::SyntaxList, size::Tuple=Base.size(v.ids))
    SyntaxList(v.graph, zeros(NodeId, size))
end

function Base.isassigned(v::SyntaxList, i::Integer)
    v.ids[i] > 0
end

function Base.append!(v::SyntaxList, exs)
    for e in exs
        push!(v, e)
    end
    v
end

function Base.append!(v::SyntaxList, exs::SyntaxList)
    check_compatible_graph(v, exs)
    append!(v.ids, exs.ids)
    v
end

function Base.push!(v::SyntaxList, id::NodeId)
    push!(v.ids, id)
end

function Base.pop!(v::SyntaxList)
    SyntaxTree(v.graph, pop!(v.ids))
end

function Base.resize!(v::SyntaxList, n)
    resize!(v.ids, n)
    v
end

function Base.empty!(v::SyntaxList)
    empty!(v.ids)
    v
end

function Base.deleteat!(v::SyntaxList, inds)
    deleteat!(v.ids, inds)
    v
end

function Base.copy(v::SyntaxList)
    SyntaxList(v.graph, copy(v.ids))
end

function Base.filter(f, exs::SyntaxList)
    out = SyntaxList(syntax_graph(exs))
    for ex in exs
        if f(ex)
            push!(out, ex)
        end
    end
    out
end

# Would like the following to be an overload of Base.map() ... but need
# somewhat arcane trickery to ensure that this only tries to collect into a
# SyntaxList when `f` yields a SyntaxTree.
#
# function mapsyntax(f, exs::SyntaxList)
#     out = SyntaxList(syntax_graph(exs))
#     for ex in exs
#         push!(out, f(ex))
#     end
#     out
# end

# TODO: forgot to support vcat (i.e. newlines in patterns currently require a
# double-semicolon continuation)

# TODO: SyntaxList pattern matching could take similar syntax and use most of
# the same machinery

raw"""
Simple SyntaxTree pattern matching

```
@stm syntax_tree begin
    pattern1 -> result1
    (pattern2, when=cond2) -> result2
    (pattern3, when=cond3, run=run3, when=cond4) -> result3
    ...
end
```

Returns the first result where its corresponding pattern matches `syntax_tree`
and each extra `cond` is true.  Throws an error if no match is found.

This macro (especially `when` and `run`) takes heavy inspiration from [Racket's
pattern matching](https://docs.racket-lang.org/reference/match.html), but with a
significantly less featureful pattern language.

## Patterns

A pattern is used as both a conditional (does this syntax tree have a certain
structure?) and a `let` (bind trees to these names if so).  Each pattern uses a
limited version of the @ast syntax:

```
<pattern> = <tree_identifier>
          | [K"<kind>" <pattern>*]
          | [K"<kind>" <pattern>* <list_identifier>... <pattern>*]

# note "*" is the meta-operator meaning one or more, and "..." is literal
```

where a `[K"k" p1 p2 ps...]` form matches any tree with kind `k` and >=2
children (bound to `p1` and `p2`), and `ps` is bound to the possibly-empty
SyntaxList of children `3:end`.  Identifiers (except `_`) can't be re-used, but
may check for some form of tree equivalence in a future implementation.

## Extra conditions: `when`, `run`

Like an escape hatch to the structure-matching mechanism.  `when=cond` requires
`cond`'s value be `true` for this pattern to match.  `run=code` simply evaluates
`code`, usually to bind variables or debug the matching process.

`when` and `run` clauses may appear multiple times in any order after the
pattern.  They are executed left-to-right, stopping if any `when=cond` evaluates
to false.  These may not mutate the object being matched.

## Scope of variables

Every `(pattern, extras...) -> result` introduces a local scope.  Identifiers in
the pattern are let-bound when evaluating `extras` and `result`. Any `extra` can
introduce variables for use in later `extras` and `result`.  User code in
`extras` and `result` can refer to outer variables.

## Example

```
julia> st = JuliaSyntax.parsestmt(JuliaLowering.SyntaxTree, "function foo(x,y,z); x; end")
julia> JuliaLowering.@stm st begin
    [K"function" [K"call" fname args... [K"parameters" kws...]] body] ->
        "has kwargs: $(kws)"
    [K"function" fname] ->
        "zero-method function $fname"
    [K"function" [K"call" fname args...] body] ->
        "normal function $fname"
    ([K"=" [K"call" _...] _...], when=(args=if_valid_get_args(st[1]); !isnothing(args))) ->
        "deprecated call-equals form with args $args"
    (_, run=show("printf debugging is great")) -> "something else"
    _ -> "something else"
end
"normal function foo"
```
"""
macro stm(st, pats)
    _stm(__source__, st, pats; debug=false)
end

"Like `@stm`, but prints a trace during matching."
macro stm_debug(st, pats)
    _stm(__source__, st, pats; debug=true)
end

function _stm(line::LineNumberNode, st, pats; debug=false)
    _stm_check_usage(pats)
    # We leave most code untouched, so the user probably wants esc(output)
    st_gs, result_gs = gensym("st"), gensym("result")
    out_blk = Expr(:let,
                   Expr(:block, :($st_gs = $st::SyntaxTree), :($result_gs = nothing)),
                   Expr(:if, false, nothing))
    needs_else = out_blk.args[2].args
    for per in pats.args
        per isa LineNumberNode && (line = per; continue)
        p, extras, result = _stm_destruct_pat(Base.remove_linenums!(per))
        # We need to let-bind patvars in both extras and the result, so result
        # needs to live in the first argument of :if with the extra conditions.
        e_check = Expr(:&&)
        for (ek, ev) in extras
            push!(e_check.args, ek === :when ? ev : Expr(:block, ev, true))
        end
        # final arg to e_check: successful match
        push!(e_check.args, Expr(:block, line, :($result_gs = $result), true))
        case = Expr(:elseif,
            Expr(:&&, :(JuliaLowering._stm_matches($(Expr(:quote, p)), $st_gs, $debug)),
                 Expr(:let, _stm_assigns(p, st_gs), e_check)),
            result_gs)
        push!(needs_else, case)
        needs_else = needs_else[3].args
    end
    push!(needs_else, :(throw("No match found for $($st_gs) at $($(string(line)))")))
    return esc(out_blk)
end

function _stm_destruct_pat(per)
    pe, r = per.args[1:2]
    return !Meta.isexpr(pe, :tuple) ? (pe, Tuple[], r) :
        let extras = pe.args[2:end]
            (pe.args[1], Tuple[(e.args[1], e.args[2]) for e in extras], r)
        end
end

function _stm_matches(p::Union{Symbol, Expr}, st, debug=false, indent="")
    if p isa Symbol
        debug && printstyled(indent, "$p = $st\n"; color=:yellow)
        return true
    elseif Meta.isexpr(p, (:vect, :hcat))
        p_kind = Kind(p.args[1].args[3])
        kind_ok = p_kind === kind(st)
        if !kind_ok
            debug && printstyled(indent, "[kind]: $(kind(st))!=$p_kind\n"; color=:red)
            return false
        end
        p_args = filter(e->!(e isa LineNumberNode), p.args)[2:end]
        dots_i = findfirst(x->Meta.isexpr(x, :(...)), p_args)
        dots_start = something(dots_i, length(p_args) + 1)
        n_after = length(p_args) - dots_start
        npats = dots_start + n_after
        n_ok = (isnothing(dots_i) ? numchildren(st) === npats : numchildren(st) >= npats - 1)
        if !n_ok
            debug && printstyled(indent, "[numc]: $(numchildren(st))!=$npats\n"; color=:red)
            return false
        end
        all_ok = all(i->_stm_matches(p_args[i], st[i], debug, indent*"  "), 1:dots_start-1) &&
            all(i->_stm_matches(p_args[end-i], st[end-i], debug, indent*"  "), n_after-1:-1:0)
        debug && printstyled(indent, st, all_ok ? " matched\n" : " not matched\n";
                             color=(all_ok ? :green : :red))
        return all_ok
    end
    @assert false
end

# Assuming _stm_matches, construct an Expr that assigns syms to SyntaxTrees.
# Note st_rhs_expr is a ref-expr with a SyntaxTree/List value (in context).
function _stm_assigns(p, st_rhs_expr; assigns=Expr(:block))
    if p isa Symbol && p != :_
        push!(assigns.args, Expr(:(=), p, st_rhs_expr))
    elseif p isa Expr
        p_args = filter(e->!(e isa LineNumberNode), p.args)[2:end]
        dots_i = findfirst(x->Meta.isexpr(x, :(...)), p_args)
        dots_start = something(dots_i, length(p_args) + 1)
        n_after = length(p_args) - dots_start
        for i in 1:dots_start-1
            _stm_assigns(p_args[i], :($st_rhs_expr[$i]); assigns)
        end
        if !isnothing(dots_i)
            _stm_assigns(p_args[dots_i].args[1],
                         :($st_rhs_expr[$dots_i:end-$n_after]); assigns)
            for i in n_after-1:-1:0
                _stm_assigns(p_args[end-i], :($st_rhs_expr[end-$i]); assigns)
            end
        end
    end
    return assigns
    @assert false
end

# Check for correct pattern syntax.  Not needed outside of development.
function _stm_check_usage(pats)
    function _stm_check_pattern(p; syms=Set{Symbol}())
        if Meta.isexpr(p, :(...), 1)
            p = p.args[1]
            @assert(p isa Symbol, "Expected symbol before `...` in $p")
        end
        if p isa Symbol
            # No support for duplicate syms for now (user is either looking for
            # some form of equality we don't implement, or they made a mistake)
            dup = p in syms && p !== :_
            push!(syms, p)
            return !dup || @assert(false, "invalid duplicate non-underscore identifier $p")
        end
        return (Meta.isexpr(p, :vect, 1) ||
            (Meta.isexpr(p, :hcat) &&
            isnothing(@assert(count(x->Meta.isexpr(x, :(...)), p.args[2:end]) <= 1,
                              "Multiple `...` in a pattern is ambiguous")) &&
            all(x->_stm_check_pattern(x; syms), p.args[2:end])) &&
            # This exact syntax is not necessary since the kind can't be
            # provided by a variable, but requiring [K"kinds"] is consistent.
            Meta.isexpr(p.args[1], :macrocall, 3) &&
            p.args[1].args[1] === Symbol("@K_str") && p.args[1].args[3] isa String)
    end

    @assert Meta.isexpr(pats, :block) "Usage: @st_match st begin; ...; end"
    for per in filter(e->!isa(e, LineNumberNode), pats.args)
        @assert(Meta.isexpr(per, :(->), 2), "Expected pat -> res, got malformed pair: $per")
        if Meta.isexpr(per.args[1], :tuple)
            @assert length(per.args[1].args) >= 2 "Unnecessary tuple in $(per.args[1])"
            for e in per.args[1].args[2:end]
                @assert(Meta.isexpr(e, :(=), 2) && e.args[1] in (:when, :run),
                        "Expected `when=<cond>` or `run=<stmts>`, got $e")
            end
            p = per.args[1].args[1]
        else
            p = per.args[1]
        end
        @assert _stm_check_pattern(p) "Malformed pattern: $p"
    end
end
