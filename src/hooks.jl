#-------------------------------------------------------------------------------
# Experimental functionality that should be moved into Base / Core when it
# seems ready

baremodule _Core

using Base
using Core: CodeInfo

abstract type CompilerFrontend
end

_compiler_frontend = nothing

function _set_compiler_frontend!(frontend)
    global _compiler_frontend
    old = _compiler_frontend
    _compiler_frontend = frontend
    return old
end

"""
parseall(frontend, text; filename="none")

Parse Julia code with the provided Julia compiler `frontend`.

TODO: Generalize to allow:
* Replacement of `Core._parse` hook
  - Callable from C runtime code
  - `Meta.parse()` `parseatom` and `parseall`
* Compiler diagnostics
"""
function parseall
end

# Incremental lowering API which can manage toplevel and module expressions via
# iteration. The iterator API here is oddly bespoke because `eval()` and
# lowering must pass parameters back and forth. (Lowering to inform eval about
# modules begin/end and eval to create the actual module object and pass it back.)
abstract type TopLevelCodeIterator
end

struct BeginModule
    name::Symbol
    standard_defs::Bool # If true, use `Base` and define `eval` and `include`
    location # Currently LineNumberNode but might be something else in future
end

struct EndModule
end

# Return a subtype of `TopLevelCodeIterator` which may be passed to `lower_step`
function lower_init
end

# Returns one of
# * `CodeInfo`    - top level thunk to evaluate
# * `BeginModule` - start a new module (must be paired with EndModule later in iteration)
# * `EndModule`   - finish current module
# * `Nothing`     - iteration is finished
function lower_step
end

#-------------------------------------------------------------------------------
# TODO: C entry points to make it easier for the runtime to call into parsing
# and lowering... ??
#
# function __parse(text::String, offset::Int, filename::String, rule::Symbol)
#     ex, off = parse_code(_compiler_frontend, text, filename; rule=rule)
#     svec(ex, off)
# end
#
# function __parse(text::SimpleVector, offset::Int, filename::String, rule::Symbol)
#     ?? unsafe_string(text[1], text[2])
#     ?? SubString(text[1])
#     ex, off = parse_code(_compiler_frontend, text, filename; rule=rule)
#     svec(ex, off)
# end
#
# function __lower
# end

#-------------------------------------------------------------------------------
eval(mod::Module, ex; opts...) = eval(_compiler_frontend, mod, ex; opts...)

function eval(frontend::CompilerFrontend, mod::Module, ex; mapexpr=nothing, opts...)
    iter = lower_init(_compiler_frontend, mod, ex, mapexpr; opts...)
    simple_eval(mod, iter)
end

# Barebones `eval()` based on top level iteration API
function simple_eval(mod::Module, thunk::CodeInfo)
    # TODO: @ccall jl_eval_thunk instead?
    Core.eval(mod, Expr(:thunk, thunk))
end

# Shim in case we want extend the allowed types of newmod.location
_module_loc(loc::LineNumberNode) = (loc.file, loc.line)

if VERSION >= v"1.13.0-DEV.1199" # https://github.com/JuliaLang/julia/pull/59604

function simple_eval(mod::Module, newmod::BeginModule)
    file, line = _module_loc(newmod.location)
    @ccall jl_begin_new_module(mod::Module, newmod.name::Symbol,
                               newmod.standard_defs::Cint,
                               file::Cstring, line::Cint)::Module
end

function simple_eval(mod::Module, ::EndModule)
    @ccall jl_end_new_module(mod::Module)::Cvoid
    return mod
end

function simple_eval(mod::Module, iter::TopLevelCodeIterator)
    modules = Module[]
    new_mod = nothing
    result = nothing
    while true
        thunk = lower_step(iter, Base.get_world_counter(), new_mod)
        if isnothing(thunk)
            @assert isempty(modules)
            return result
        end
        result = simple_eval(mod, thunk)
        if thunk isa BeginModule
            push!(modules, mod)
            mod = result
            new_mod = mod
        elseif thunk isa EndModule
            result = mod
            mod = pop!(modules)
            new_mod = nothing
        else
            new_mod = nothing
        end
    end
end

else

# 1.12 compat
#
# We can't easily implement the following in pre 1.13 Julia. Possibly we could
# do something using a Task to manage the stack frame of Core.eval, but we'd
# need something other than `Module` as the first agument of `simple_eval` in
# order to hold the associated channels and it would be terribly heavy weight.
#
# simple_eval(mod::Module, newmod::BeginModule)
# simple_eval(mod::Module, ::EndModule)

function simple_eval(mod::Module, iter::TopLevelCodeIterator, new_mod=nothing)
    in_new_mod = !isnothing(new_mod)
    result = nothing
    while true
        thunk = lower_step(iter, Base.get_world_counter(), new_mod)
        new_mod = nothing
        if isnothing(thunk)
            @assert !in_new_mod
            return result
        elseif thunk isa BeginModule
            file, line = _module_loc(thunk.location)
            result = Core.eval(mod,
                Expr(:module, thunk.standard_defs, thunk.name,
                     Expr(:block, LineNumberNode(line, file),
                          Expr(:call, m->simple_eval(m, iter, m), thunk.name)))
            )
        elseif thunk isa EndModule
            @assert in_new_mod
            return mod
        else
            @assert thunk isa CodeInfo
            result = simple_eval(mod, thunk)
        end
    end
end

end


#-------------------------------------------------------------------------------
function include_string(frontend::CompilerFrontend, mod::Module, code::AbstractString;
                        filename::AbstractString="string", mapexpr=nothing, opts...)
    ex = parseall(frontend, code; filename=filename)
    eval(mod, ex; mapexpr=mapexpr, opts...)
end

function include_string(mod::Module, code::AbstractString; opts...)
    include_string(_compiler_frontend, mod, code; opts...)
end

# TODO: Simple include() implementation would also be hooked up here.

#-------------------------------------------------------------------------------
# Julia's builtin flisp-based compiler frontend
struct FlispCompilerFrontend <: CompilerFrontend
end

# TODO
# function fl_parse(text::Union{Core.SimpleVector,String},
#                   filename::String, lineno, offset, options)
#     if text isa Core.SimpleVector
#         # Will be generated by C entry points jl_parse_string etc
#         text, text_len = text
#     else
#         text_len = sizeof(text)
#     end
#     ccall(:jl_fl_parse, Any, (Ptr{UInt8}, Csize_t, Any, Csize_t, Csize_t, Any),
#           text, text_len, filename, lineno, offset, options)
# end
#
# function fl_parse(text::AbstractString, filename::AbstractString, lineno, offset, options)
#     fl_parse(String(text), String(filename), lineno, offset, options)
# end
#
# function fl_lower(ex, mod::Module, filename::Union{String,Ptr{UInt8}}="none",
#                   lineno=0, world::Unsigned=typemax(Csize_t), warn::Bool=false)
#     warn = warn ? 1 : 0
#     ccall(:jl_fl_lower, Any, (Any, Any, Ptr{UInt8}, Csize_t, Csize_t, Cint),
#           ex, mod, filename, lineno, world, warn)
# end

#-------------------------------------------------------------------------------
# TODO Current default frontend: JuliaSyntax for parsing plus flisp lowering
# implementation

struct DefaultFrontend <: CompilerFrontend
end

#-------------------------------------------------------------------------------

end # module _Core


baremodule _Base

using Base

using .._Core

# TODO: Meta integration...
#
# module _Meta
#
# function parseall
#     ...
# end
#
# end

function include_string(mapexpr::Function, mod::Module,
                        code::AbstractString, filename::AbstractString="string";
                        opts...)
    # `identity` is not defined in Core - need to special case it here if we
    # want to elide Expr conversion in some cases.
    _Core.include_string(mod, code;
                         mapexpr=(mapexpr===identity ? nothing : mapexpr),
                         filename=filename,
                         opts...)
end

function include_string(mod::Module, code::AbstractString, filename::AbstractString="string";
                        opts...)
    include_string(identity, mod, code, filename; opts...)
end

"""
    include([mapexpr::Function], mod::Module, path::AbstractString)

Evaluate the contents of the input source file in the global scope of module
`mod`. Every module (except those defined with baremodule) has its own
definition of `include()` omitting the `mod` argument, which evaluates the file
in that module. Returns the result of the last evaluated expression of the
input file. During including, a task-local include path is set to the directory
containing the file. Nested calls to include will search relative to that path.
This function is typically used to load source interactively, or to combine
files in packages that are broken into multiple source files.
"""
function include(mapexpr::Function, mod::Module, path::AbstractString)
    path, prev = Base._include_dependency(mod, path)
    code = read(path, String)
    tls = task_local_storage()
    tls[:SOURCE_PATH] = path
    try
        return include_string(mapexpr, mod, code, path)
    finally
        if prev === nothing
            delete!(tls, :SOURCE_PATH)
        else
            tls[:SOURCE_PATH] = prev
        end
    end
end

function include(mod::Module, path::AbstractString)
    include(identity, mod, path)
end

end # module _Base


#-------------------------------------------------------------------------------
struct JuliaLoweringFrontend <: _Core.CompilerFrontend
    # world::UInt # TODO: fixed world age for frontend
end

function _Core.parseall(::JuliaLoweringFrontend, code::AbstractString; filename="none")
    JuliaSyntax.parseall(SyntaxTree, code; filename=filename, ignore_warnings=true)
end

struct LoweringIterator <: _Core.TopLevelCodeIterator
    # frontend::JuliaLoweringFrontend  # TODO: world age?
    ctx::MacroExpansionContext
    todo::Vector{Tuple{SyntaxTree, Bool, Int}}
    mapexpr::Any
end

function _Core.lower_init(::JuliaLoweringFrontend, mod::Module, ex, mapexpr;
                          expr_compat_mode::Bool=false)
    if !(ex isa SyntaxTree)
        ex = expr_to_syntaxtree(ex)
    else
        # TODO: Copy `ex`? We don't want the underlying graph mutated :-(
    end
    graph = ensure_macro_attributes(syntax_graph(ex))
    dummy_world = zero(UInt)
    ctx = MacroExpansionContext(graph, mod, expr_compat_mode, dummy_world)
    ex = reparent(ctx, ex)
    LoweringIterator(ctx, [(ex, false, 0)], mapexpr)
end

using ._Core: lower_step, BeginModule, EndModule

function _Core.lower_step(iter, macro_world, push_mod=nothing)
    if !isnothing(push_mod)
        push_layer!(iter.ctx, push_mod, false)
    end

    if isempty(iter.todo)
        return nothing
    end

    ex, is_module_body, child_idx = pop!(iter.todo)
    if child_idx > 0
        next_child = child_idx + 1
        if child_idx <= numchildren(ex)
            push!(iter.todo, (ex, is_module_body, next_child))
            ex = ex[child_idx]
        else
            if is_module_body
                pop_layer!(iter.ctx)
                return EndModule()
            else
                return lower_step(iter, macro_world)
            end
        end
    end

    k = kind(ex)
    if !(k in KSet"toplevel module")
        if !is_module_body && !isnothing(iter.mapexpr)
            # TODO: `mapexpr` is a pretty niche tool and in principle could be
            # generically implemented on top of expression iteration if we had
            # an option to do that without macro expansion.
            ex = iter.ctx.expr_compat_mode ?
                 expr_to_syntaxtree(iter.ctx, iter.mapexpr(Expr(ex))) :
                 iter.mapexpr(ex)
        end
        c = iter.ctx
        # Copy context in order to update macro_world
        ctx = MacroExpansionContext(c.graph, c.bindings, c.scope_layers,
                                    c.scope_layer_stack, c.expr_compat_mode, macro_world)
        ex = expand_forms_1(ctx, ex)
        k = kind(ex)
    end
    if k == K"toplevel"
        push!(iter.todo, (ex, false, 1))
        return lower_step(iter, macro_world)
    elseif k == K"module"
        name = ex[1]
        if kind(name) != K"Identifier"
            throw(LoweringError(name, "Expected module name"))
        end
        newmod_name = Symbol(name.name_val)
        body = ex[2]
        if kind(body) != K"block"
            throw(LoweringError(body, "Expected block in module body"))
        end
        std_defs = !has_flags(ex, JuliaSyntax.BARE_MODULE_FLAG)
        loc = source_location(LineNumberNode, ex)
        push!(iter.todo, (body, true, 1))
        return BeginModule(newmod_name, std_defs, loc)
    else
        # Non macro expansion parts of lowering
        ctx2, ex2 = expand_forms_2(iter.ctx, ex)
        ctx3, ex3 = resolve_scopes(ctx2, ex2)
        ctx4, ex4 = convert_closures(ctx3, ex3)
        ctx5, ex5 = linearize_ir(ctx4, ex4)
        thunk = to_lowered_expr(ex5)
        return thunk.args[1] # TODO: Remove wrapping elsewhere?
    end
end


#-------------------------------------------------------------------------------
# Simple lowering hook. Can be removed once we complete the frontend API above.
"""
Becomes `Core._lower()` upon activating JuliaLowering.

Returns an svec with the lowered code (usually expr) as its first element, and
(until integration is less experimental) whatever we want after it
"""
function core_lowering_hook(@nospecialize(code), mod::Module,
                            file="none", line=0, world=typemax(Csize_t), warn=false)
    if !(code isa SyntaxTree || code isa Expr)
        # e.g. LineNumberNode, integer...
        return Core.svec(code)
    end

    # TODO: fix in base
    file = file isa Ptr{UInt8} ? unsafe_string(file) : file
    line = !(line isa Int64) ? Int64(line) : line

    local st0 = nothing
    try
        st0 = code isa Expr ? expr_to_syntaxtree(code, LineNumberNode(line, file)) : code
        ctx1, st1 = expand_forms_1(  mod,  st0, true, world)
        ctx2, st2 = expand_forms_2(  ctx1, st1)
        ctx3, st3 = resolve_scopes(  ctx2, st2)
        ctx4, st4 = convert_closures(ctx3, st3)
        ctx5, st5 = linearize_ir(    ctx4, st4)
        ex = to_lowered_expr(st5)
        return Core.svec(ex, st5, ctx5)
    catch exc
        @info("JuliaLowering threw given input:", code=code, st0=st0, file=file, line=line, mod=mod)
        rethrow(exc)

        # TODO: Re-enable flisp fallback once we're done collecting errors
        # @error("JuliaLowering failed — falling back to flisp!",
        #        exception=(exc,catch_backtrace()),
        #        code=code, file=file, line=line, mod=mod)
        # return Base.fl_lower(code, mod, file, line, world, warn)
    end
end

const _has_v1_13_hooks = isdefined(Core, :_lower)

function activate!(enable=true)
    if !_has_v1_13_hooks
        error("Cannot use JuliaLowering without `Core._lower` binding or in $VERSION < 1.13")
    end

    if enable
        Core._setlowerer!(core_lowering_hook)
    else
        Core._setlowerer!(Base.fl_lower)
    end
end

#-------------------------------------------------------------------------------

_Core._set_compiler_frontend!(JuliaLoweringFrontend())

# Pull implementations from _Base/_Core into JuliaLowering for now
# (Assumes frontend is in _Core not Core.)
@fzone "JL: eval" function eval(mod::Module, ex; opts...)
    _Core.eval(mod, ex; opts...)
end

const include = _Base.include
const include_string = _Base.include_string
