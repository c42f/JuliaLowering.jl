"""
Metadata about a binding
"""
struct BindingInfo
    id::IdTag                 # Unique integer identifying this binding
    name::String
    kind::Symbol              # :local :global :argument :static_parameter
    node_id::Int              # ID of associated K"BindingId" node in the syntax graph
    mod::Union{Nothing,Module} # Set when `kind === :global`
    type::Union{Nothing,SyntaxTree} # Type, for bindings declared like x::T = 10
    is_const::Bool            # Constant, cannot be reassigned
    is_ssa::Bool              # Single assignment, defined before use
    is_captured::Bool         # Variable is captured by some lambda
    is_always_defined::Bool   # A local that we know has an assignment that dominates all usages (is never undef)
    is_internal::Bool         # True for internal bindings generated by the compiler
    is_ambiguous_local::Bool  # Local, but would be global in soft scope (ie, the REPL)
    is_nospecialize::Bool     # @nospecialize on this argument (only valid for kind == :argument)
end

function BindingInfo(id::IdTag, name::AbstractString, kind::Symbol, node_id::Integer;
                     mod::Union{Nothing,Module} = nothing,
                     type::Union{Nothing,SyntaxTree} = nothing,
                     is_const::Bool = false,
                     is_ssa::Bool = false,
                     is_captured::Bool = false,
                     is_always_defined::Bool = is_ssa,
                     is_internal::Bool = false,
                     is_ambiguous_local::Bool = false,
                     is_nospecialize::Bool = false)
    BindingInfo(id, name, kind, node_id, mod, type, is_const, is_ssa, is_captured, is_always_defined,
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

next_binding_id(bindings::Bindings) = length(bindings.info) + 1

function add_binding(bindings::Bindings, binding)
    if next_binding_id(bindings) != binding.id
        error("Use next_binding_id() to create a valid binding id")
    end
    push!(bindings.info, binding)
end

function _binding_id(id::Integer)
    id
end

function _binding_id(ex::SyntaxTree)
    @chk kind(ex) == K"BindingId"
    ex.var_id
end

function update_binding!(bindings::Bindings, x;
        type=nothing, is_const=nothing, is_always_defined=nothing, is_captured=nothing)
    id = _binding_id(x)
    b = lookup_binding(bindings, id)
    bindings.info[id] = BindingInfo(
        b.id,
        b.name,
        b.kind,
        b.node_id,
        b.mod,
        isnothing(type) ? b.type : type,
        isnothing(is_const) ? b.is_const : is_const,
        b.is_ssa,
        isnothing(is_captured) ? b.is_captured : is_captured,
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

function new_binding(ctx::AbstractLoweringContext, srcref::SyntaxTree,
                     name::AbstractString, kind::Symbol; kws...)
    binding_id = next_binding_id(ctx.bindings)
    ex = @ast ctx srcref binding_id::K"BindingId"
    add_binding(ctx.bindings, BindingInfo(binding_id, name, kind, ex._id; kws...))
    ex
end

# Create a new SSA binding
function ssavar(ctx::AbstractLoweringContext, srcref, name="tmp")
    nameref = makeleaf(ctx, srcref, K"Identifier", name_val=name)
    new_binding(ctx, nameref, name, :local; is_ssa=true, is_internal=true)
end

# Create a new local mutable binding or lambda argument
function new_local_binding(ctx::AbstractLoweringContext, srcref, name; kind=:local, kws...)
    @assert kind === :local || kind === :argument
    nameref = makeleaf(ctx, srcref, K"Identifier", name_val=name)
    ex = new_binding(ctx, nameref, name, kind; is_internal=true, kws...)
    add_lambda_local!(ctx, ex.var_id)
    ex
end

function new_global_binding(ctx::AbstractLoweringContext, srcref, name, mod; kws...)
    nameref = makeleaf(ctx, srcref, K"Identifier", name_val=name)
    new_binding(ctx, nameref, name, :global; is_internal=true, mod=mod, kws...)
end

function binding_ex(ctx::AbstractLoweringContext, id::IdTag)
    # Reconstruct the SyntaxTree for this binding. We keep only the node_id
    # here, because that's got a concrete type. Whereas if we stored SyntaxTree
    # that would contain the type of the graph used in the pass where the
    # bindings were created and we'd need to call reparent(), etc.
    SyntaxTree(syntax_graph(ctx), lookup_binding(ctx, id).node_id)
end

