# Runtime support functionality.
#
# Lowering generates code which uses these functions and types but it doesn't
# call them directly.
#
# These should probably move to `Core` at some point?

struct InterpolationContext{Graph} <: AbstractLoweringContext
    graph::Graph
    values::Tuple
    current_index::Ref{Int}
end

function _contains_active_interp(ex, depth)
    k = kind(ex)
    if k == K"$" && depth == 0
        return true
    end
    inner_depth = k == K"quote" ? depth + 1 :
                  k == K"$"     ? depth - 1 :
                  depth
    return any(_contains_active_interp(c, inner_depth) for c in children(ex))
end

# Produce interpolated node for `$x` syntax
function _interpolated_value(ctx, srcref, ex)
    if ex isa SyntaxTree
        if !is_compatible_graph(ctx, ex)
            ex = copy_ast(ctx, ex)
        end
        append_sourceref(ctx, ex, srcref)
    else
        makeleaf(ctx, srcref, K"Value", ex)
    end
end

function _interpolate_ast(ctx::InterpolationContext, ex, depth)
    if ctx.current_index[] > length(ctx.values) || !_contains_active_interp(ex, depth)
        return ex
    end

    # We have an interpolation deeper in the tree somewhere - expand to an
    # expression 
    inner_depth = kind(ex) == K"quote" ? depth + 1 :
                  kind(ex) == K"$"     ? depth - 1 :
                  depth
    expanded_children = SyntaxList(ctx)
    for e in children(ex)
        if kind(e) == K"$" && inner_depth == 0
            vals = ctx.values[ctx.current_index[]]::Tuple
            ctx.current_index[] += 1
            for (i,v) in enumerate(vals)
                srcref = numchildren(e) == 1 ? e : e[i]
                push!(expanded_children, _interpolated_value(ctx, srcref, v))
            end
        else
            push!(expanded_children, _interpolate_ast(ctx, e, inner_depth))
        end
    end

    makenode(ctx, ex, head(ex), expanded_children)
end

function interpolate_ast(ex, values...)
    # Construct graph for interpolation context. We inherit this from the macro
    # context where possible by detecting it using __macro_ctx__. This feels
    # hacky though.
    #
    # Perhaps we should use a ScopedValue for this instead or get it from
    # the macro __context__? Nothing feels great here.
    graph = nothing
    for vals in values
        for v in vals
            if v isa SyntaxTree && hasattr(syntax_graph(v), :__macro_ctx__)
                graph = syntax_graph(v)
                break
            end
        end
    end
    if isnothing(graph)
        graph = ensure_attributes(SyntaxGraph(), kind=Kind, syntax_flags=UInt16, source=SourceAttrType,
                                  value=Any, name_val=String, scope_layer=LayerId)
    end
    ctx = InterpolationContext(graph, values, Ref(1))
    # We must copy the AST into our context to use it as the source reference
    # of generated expressions.
    ex1 = copy_ast(ctx, ex)
    if kind(ex1) == K"$"
        @assert length(values) == 1
        vs = values[1]
        if length(vs) > 1
            # :($($(xs...))) where xs is more than length 1
            throw(LoweringError(ex1, "More than one value in bare `\$` expression"))
        end
        _interpolated_value(ctx, ex1, only(vs))
    else
        _interpolate_ast(ctx, ex1, 0)
    end
end

# Construct new bare module including only the "default names"
#
#     using Core
#     const modname = modval
#     public modname
#
# And run statments in the toplevel expression `body`
function eval_module(parentmod, modname, body)
    # Here we just use `eval()` with an Expr.
    # If we wanted to avoid this we'd need to reproduce a lot of machinery from
    # jl_eval_module_expr()
    #
    # 1. Register / deparent toplevel modules
    # 2. Set binding in parent module
    # 3. Deal with replacing modules
    #    * Warn if replacing
    #    * Root old module being replaced
    # 4. Run __init__
    #    * Also run __init__ for any children after parent is defined
    # mod = @ccall jl_new_module(Symbol(modname)::Symbol, parentmod::Module)::Any
    # ...
    name = Symbol(modname)
    eval(parentmod, :(
        baremodule $name
            $eval($name, $body)
        end
    ))
end

# Evaluate content of `import` or `using` statement
function module_import(into_mod::Module, is_using::Bool,
                       from_mod::Union{Nothing,Core.SimpleVector}, paths::Core.SimpleVector)
    # For now, this function converts our lowered representation back to Expr
    # and calls eval() to avoid replicating all of the fiddly logic in
    # jl_toplevel_eval_flex.
    # TODO: ccall Julia runtime functions directly?
    #   * jl_module_using jl_module_use_as
    #   * import_module jl_module_import_as
    path_args = []
    i = 1
    while i < length(paths)
        nsyms = paths[i]::Int
        n = i + nsyms
        path = Expr(:., [Symbol(paths[i+j]::String) for j = 1:nsyms]...)
        as_name = paths[i+nsyms+1]
        push!(path_args, isnothing(as_name) ? path :
                         Expr(:as, path, Symbol(as_name)))
        i += nsyms + 2
    end
    ex = if isnothing(from_mod)
        Expr(is_using ? :using : :import,
             path_args...)
    else
        from_path = Expr(:., [Symbol(s::String) for s in from_mod]...)
        Expr(is_using ? :using : :import,
             Expr(:(:), from_path, path_args...))
    end
    eval(into_mod, ex)
    nothing
end

# Return the current exception. In JuliaLowering we use this rather than the
# special form `K"the_exception"` to reduces the number of special forms.
Base.@assume_effects :removable :nothrow function current_exception()
    @ccall jl_current_exception(current_task()::Any)::Any
end

function _bind_func_docs!(f, docstr, method_metadata::Core.SimpleVector)
    mod = parentmodule(f)
    bind = Base.Docs.Binding(mod, nameof(f))
    full_sig = method_metadata[1]
    arg_sig = Tuple{full_sig[2:end]...}
    lineno = method_metadata[3]
    metadata = Dict{Symbol, Any}(
        :linenumber => lineno.line,
        :module => mod,
    )
    if !isnothing(lineno.file)
        push!(metadata, :path => string(lineno.file))
    end
    Docs.doc!(mod, bind, Base.Docs.docstr(docstr, metadata), arg_sig)
end

function bind_docs!(f::Function, docstr, method_metadata::Core.SimpleVector)
    _bind_func_docs!(f, docstr, method_metadata)
end

# Document constructors
function bind_docs!(::Type{Type{T}}, docstr, method_metadata::Core.SimpleVector) where T
    _bind_func_docs!(T, docstr, method_metadata)
end

function bind_docs!(type::Type, docstr, method_metadata::Core.SimpleVector)
    _bind_func_docs!(type, docstr, method_metadata)
end

function bind_docs!(type::Type, docstr, lineno::LineNumberNode; field_docs=Core.svec())
    mod = parentmodule(type)
    bind = Base.Docs.Binding(mod, nameof(type))
    metadata = Dict{Symbol, Any}(
        :linenumber => lineno,
        :module => mod,
    )
    if !isnothing(lineno.file)
        push!(metadata, :path => string(lineno.file))
    end
    if !isempty(field_docs)
        fd = Dict{Symbol, Any}()
        fns = fieldnames(type)
        for i = 1:2:length(field_docs)
            fd[fns[field_docs[i]]] = field_docs[i+1]
        end
        metadata[:fields] = fd
    end
    Docs.doc!(mod, bind, Base.Docs.docstr(docstr, metadata), Union{})
end

#-------------------------------------------------------------------------------
# The following functions are used by lowering to inspect Julia's state.

# Get the binding for `name` if one is already resolved in module `mod`. Note
# that we cannot use `isdefined(::Module, ::Symbol)` here, because that causes
# binding resolution which is a massive side effect we must avoid in lowering.
function _get_module_binding(mod, name; create=false)
    b = @ccall jl_get_module_binding(mod::Module, name::Symbol, create::Cint)::Ptr{Core.Binding}
    b == C_NULL ? nothing : unsafe_pointer_to_objref(b)
end

# Return true if a `name` is defined in and *by* the module `mod`.
# Has no side effects, unlike isdefined()
#
# (This should do what fl_defined_julia_global does for flisp lowering)
function is_defined_and_owned_global(mod, name)
    b = _get_module_binding(mod, name)
    !isnothing(b) && isdefined(b, :owner) && b.owner === b
end

# Return true if `name` is defined in `mod`, the sense that accessing it is nothrow.
# Has no side effects, unlike isdefined()
#
# (This should do what fl_nothrow_julia_global does for flisp lowering)
function is_defined_nothrow_global(mod, name)
    b = _get_module_binding(mod, name)
    !isnothing(b) && isdefined(b, :owner) || return false
    isdefined(b.owner, :value)
end

# "Reserve" a binding: create the binding if it doesn't exist but do not assign
# to it.
function reserve_module_binding(mod, name)
    # TODO: Fix the race condition here: We should really hold the Module's
    # binding lock during this test-and-set type operation. But the binding
    # lock is only accessible from C. See also the C code in
    # `fl_module_unique_name`.
    if _get_module_binding(mod, name; create=false) === nothing
        _get_module_binding(mod, name; create=true) !== nothing
    else
        return false
    end
end

#-------------------------------------------------------------------------------
# The following are versions of macros from Base which act as "standard syntax
# extensions" with special semantics known to lowering.
#
# In order to implement these here without getting into bootstrapping
# difficulties, we just write them as plain old macro-named functions and add
# the required __context__ argument ourselves.
#
# TODO: @inline, @noinline, @inbounds, @simd, @ccall, @isdefined
#
# TODO: Eventually we should move these to proper `macro` definitions and use
# JuliaLowering.include() or something, then we'll be in the fun little
# world of bootstrapping but it shouldn't be too painful :)

function _apply_nospecialize(ctx, ex)
    k = kind(ex)
    if k == K"Identifier" || k == K"Placeholder" || k == K"tuple"
        setmeta(ex; nospecialize=true)
    elseif k == K"..." || k == K"::" || k == K"="
        if k == K"::" && numchildren(ex) == 1
            ex = @ast ctx ex [K"::" "_"::K"Placeholder" ex[1]]
        end
        mapchildren(c->_apply_nospecialize(ctx, c), ctx, ex, 1:1)
    else
        throw(LoweringError(ex, "Invalid function argument"))
    end
end

function Base.var"@nospecialize"(__context__::MacroContext, ex)
    _apply_nospecialize(__context__, ex)
end

function Base.var"@atomic"(__context__::MacroContext, ex)
    @chk kind(ex) == K"Identifier" || kind(ex) == K"::" (ex, "Expected identifier or declaration")
    @ast __context__ __context__.macrocall [K"atomic" ex]
end

function Base.var"@label"(__context__::MacroContext, ex)
    @chk kind(ex) == K"Identifier"
    @ast __context__ ex ex=>K"symbolic_label"
end

function Base.var"@goto"(__context__::MacroContext, ex)
    @chk kind(ex) == K"Identifier"
    @ast __context__ ex ex=>K"symbolic_goto"
end

function Base.var"@locals"(__context__::MacroContext)
    @ast __context__ __context__.macrocall [K"extension" "locals"::K"Symbol"]
end

function Base.var"@isdefined"(__context__::MacroContext, ex)
    @ast __context__ __context__.macrocall [K"isdefined" ex]
end

# The following `@islocal` and `@inert` are macros for special syntax known to
# lowering which don't exist in Base but arguably should.
#
# For now we have our own versions
function var"@islocal"(__context__::MacroContext, ex)
    @chk kind(ex) == K"Identifier"
    @ast __context__ __context__.macrocall [K"extension"
        "islocal"::K"Symbol"
        ex
    ]
end

"""
A non-interpolating quoted expression.

For example,

```julia
@inert quote
    \$x
end
```

does not take `x` from the surrounding scope - instead it leaves the
interpolation `\$x` intact as part of the expression tree.

TODO: What is the correct way for `@inert` to work? ie which of the following
should work?

```julia
@inert quote
   body
end

@inert begin
   body
end

@inert x

@inert \$x
```

The especially tricky cases involve nested interpolation ...
```julia
quote
    @inert \$x
end

@inert quote
    quote
        \$x
    end
end

@inert quote
    quote
        \$\$x
    end
end
```

etc. Needs careful thought - we should probably just copy what lisp does with
quote+quasiquote 😅
"""
function var"@inert"(__context__::MacroContext, ex)
    @chk kind(ex) == K"quote"
    @ast __context__ __context__.macrocall [K"inert" ex]
end

