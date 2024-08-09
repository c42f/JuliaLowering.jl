const NodeId = Int

"""
Directed graph with arbitrary attributes on nodes. Used here for representing
one or several syntax trees.
"""
struct SyntaxGraph{Attrs}
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

function _show_attrs(io, attributes::Dict)
    show(io, MIME("text/plain"), attributes)
end
function _show_attrs(io, attributes::NamedTuple)
    show(io, MIME("text/plain"), Dict(pairs(attributes)...))
end

function attrnames(graph::SyntaxGraph)
    keys(graph.attributes)
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
        else
            graph.attributes[k] = Dict{NodeId,v}()
        end
    end
    graph
end

function ensure_attributes(graph::SyntaxGraph; kws...)
    g = SyntaxGraph(graph.edge_ranges, graph.edges, Dict(pairs(graph.attributes)...))
    ensure_attributes!(g; kws...)
    freeze_attrs(g)
end

function delete_attributes(graph::SyntaxGraph, attr_names...)
    attributes = Dict(pairs(graph.attributes)...)
    for name in attr_names
        delete!(attributes, name)
    end
    SyntaxGraph(graph.edge_ranges, graph.edges, (; pairs(attributes)...))
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

# TODO: Probably terribly non-inferrable?
function setattr!(graph::SyntaxGraph, id; attrs...)
    for (k,v) in pairs(attrs)
        getattr(graph, k)[id] = v
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
    graph.kind[id] = kind(h)
    f = flags(h)
    if f != 0
        graph.syntax_flags[id] = f
    end
end

function sethead!(graph, id::NodeId, k::Kind)
    graph.kind[id] = k
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
        error("Property `$name[$_id]` not found")
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
JuliaSyntax.source_location(src::LineNumberNode, byte_index::Integer) = (src.line, 0)
JuliaSyntax.source_location(::Type{LineNumberNode}, src::LineNumberNode, byte_index::Integer) = src
JuliaSyntax.filename(src::LineNumberNode) = string(src.file)

function JuliaSyntax.highlight(io::IO, src::LineNumberNode; note="")
    print(io, src, " - ", note, "\n")
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
    id = _convert_nodes(freeze_attrs(graph), node)
    return SyntaxTree(graph, id)
end

function SyntaxTree(node::SyntaxNode)
    return SyntaxTree(SyntaxGraph(), node)
end

attrsummary(name, value) = string(name)
attrsummary(name, value::Number) = "$name=$value"

function _value_string(ex)
    k = kind(ex)
    str = k == K"Identifier" || k == K"MacroName" || is_operator(k) ? ex.name_val :
          k == K"Placeholder" ? ex.name_val :
          k == K"SSAValue"    ? "%"                   :
          k == K"BindingId"   ? "#"                   :
          k == K"label"       ? "label"               :
          k == K"core"        ? "core.$(ex.name_val)" :
          k == K"top"         ? "top.$(ex.name_val)"  :
          k == K"Symbol"      ? ":$(ex.name_val)" :
          k == K"globalref"   ? "$(ex.mod).$(ex.name_val)" :
          k == K"slot"        ? "slot" :
          k == K"symbolic_label" ? "label:$(ex.name_val)" :
          repr(get(ex, :value, nothing))
    id = get(ex, :var_id, nothing)
    if isnothing(id)
        id = get(ex, :id, nothing)
    end
    if !isnothing(id)
        idstr = replace(string(id),
                        "0"=>"₀", "1"=>"₁", "2"=>"₂", "3"=>"₃", "4"=>"₄",
                        "5"=>"₅", "6"=>"₆", "7"=>"₇", "8"=>"₈", "9"=>"₉")
        str = "$(str).$idstr"
    end
    if k == K"slot" || k == K"BindingId"
        p = provenance(ex)[1]
        while kind(p) != K"Identifier"
            p = provenance(p)[1]
        end
        str = "$(str)/$(p.name_val)"
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

function JuliaSyntax._expr_leaf_val(ex::SyntaxTree)
    name = get(ex, :name_val, nothing)
    if !isnothing(name)
        Symbol(name)
    else
        ex.value
    end
end

Base.Expr(ex::SyntaxTree) = JuliaSyntax.to_expr(ex)

#-------------------------------------------------------------------------------
# Lightweight vector of nodes ids with associated pointer to graph stored separately.
struct SyntaxList{GraphType, NodeIdVecType} <: AbstractVector{SyntaxTree}
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
    check_same_graph(v, ex)
    v.ids[i] = ex._id
end

function Base.setindex!(v::SyntaxList, id::NodeId, i::Int)
    v.ids[i] = id
end

function Base.push!(v::SyntaxList, ex::SyntaxTree)
    check_same_graph(v, ex)
    push!(v.ids, ex._id)
end

function Base.append!(v::SyntaxList, exs)
    for e in exs
        push!(v, e)
    end
    v
end

function Base.append!(v::SyntaxList, exs::SyntaxList)
    check_same_graph(v, exs)
    append!(v.ids, exs.ids)
    v
end

function Base.push!(v::SyntaxList, id::NodeId)
    push!(v.ids, id)
end

function Base.pop!(v::SyntaxList)
    SyntaxTree(v.graph, pop!(v.ids))
end

