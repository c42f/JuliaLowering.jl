#-------------------------------------------------------------------------------
# Lowering pass 5: Flatten to linear IR

function is_simple_atom(ctx, ex)
    k = kind(ex)
    # TODO flisp thismodule head?
    is_literal(k) || k == K"Symbol" || k == K"Value" || is_ssa(ctx, ex) ||
        (k == K"core" && ex.name_val == "nothing")
end

# N.B.: This assumes that resolve-scopes has run, so outerref is equivalent to
# a global in the current scope.
function is_valid_ir_argument(ctx, ex)
    k = kind(ex)
    return is_simple_atom(ctx, ex)
    # FIXME ||
           #(k == K"outerref" && nothrow_julia_global(ex[1]))  ||
           #(k == K"globalref" && nothrow_julia_global(ex))    ||
           #(k == K"quote" || k = K"inert" || k == K"top" ||
            #k == K"core" || k == K"slot" || k = K"static_parameter")
end

function is_ssa(ctx, ex)
    kind(ex) == K"BindingId" && lookup_binding(ctx, ex).is_ssa
end

# Target to jump to, including info on try handler nesting and catch block
# nesting
struct JumpTarget{GraphType}
    label::SyntaxTree{GraphType}
    handler_token_stack::SyntaxList{GraphType, Vector{NodeId}}
    catch_token_stack::SyntaxList{GraphType, Vector{NodeId}}
end

function JumpTarget(label::SyntaxTree{GraphType}, ctx) where {GraphType}
    JumpTarget{GraphType}(label, copy(ctx.handler_token_stack), copy(ctx.catch_token_stack))
end

struct JumpOrigin{GraphType}
    goto::SyntaxTree{GraphType}
    index::Int
    handler_token_stack::SyntaxList{GraphType, Vector{NodeId}}
    catch_token_stack::SyntaxList{GraphType, Vector{NodeId}}
end

function JumpOrigin(goto::SyntaxTree{GraphType}, index, ctx) where {GraphType}
    JumpOrigin{GraphType}(goto, index, copy(ctx.handler_token_stack), copy(ctx.catch_token_stack))
end

struct FinallyHandler{GraphType}
    tagvar::SyntaxTree{GraphType}
    target::JumpTarget{GraphType}
    exit_actions::Vector{Tuple{Symbol,Union{Nothing,SyntaxTree{GraphType}}}}
end

function FinallyHandler(tagvar::SyntaxTree{GraphType}, target::JumpTarget) where {GraphType}
    FinallyHandler{GraphType}(tagvar, target,
        Vector{Tuple{Symbol, Union{Nothing,SyntaxTree{GraphType}}}}())
end


"""
Context for creating linear IR.

One of these is created per lambda expression to flatten the body down to
a sequence of statements (linear IR).
"""
struct LinearIRContext{GraphType} <: AbstractLoweringContext
    graph::GraphType
    code::SyntaxList{GraphType, Vector{NodeId}}
    bindings::Bindings
    next_label_id::Ref{Int}
    is_toplevel_thunk::Bool
    lambda_locals::Set{IdTag}
    return_type::Union{Nothing, SyntaxTree{GraphType}}
    break_targets::Dict{String, JumpTarget{GraphType}}
    handler_token_stack::SyntaxList{GraphType, Vector{NodeId}}
    catch_token_stack::SyntaxList{GraphType, Vector{NodeId}}
    finally_handlers::Vector{FinallyHandler{GraphType}}
    symbolic_jump_targets::Dict{String,JumpTarget{GraphType}}
    symbolic_jump_origins::Vector{JumpOrigin{GraphType}}
    mod::Module
end

function LinearIRContext(ctx, is_toplevel_thunk, lambda_locals, return_type)
    graph = syntax_graph(ctx)
    rett = isnothing(return_type) ? nothing : reparent(graph, return_type)
    GraphType = typeof(graph)
    LinearIRContext(graph, SyntaxList(ctx), ctx.bindings, Ref(0),
                    is_toplevel_thunk, lambda_locals, rett,
                    Dict{String,JumpTarget{GraphType}}(), SyntaxList(ctx), SyntaxList(ctx),
                    Vector{FinallyHandler{GraphType}}(), Dict{String,JumpTarget{GraphType}}(),
                    Vector{JumpOrigin{GraphType}}(), ctx.mod)
end

# FIXME: BindingId subsumes many things so need to assess what that means for these predicates.
# BindingId can be
#   - local variable (previously K"Identifier")
#   - implicit global variables in current module (previously K"Identifier")
#   - globalref - from macros
#
# BindingId could also subsume
#   - top,core

function is_valid_body_ir_argument(ctx, ex)
    is_valid_ir_argument(ctx, ex) && return true
    return false
    # FIXME
    k = kind(ex)
    return k == K"BindingId" && # Arguments are always defined slots
        TODO("vinfo-table stuff")
end

function is_simple_arg(ctx, ex)
    k = kind(ex)
    return is_simple_atom(ctx, ex) || k == K"BindingId" || k == K"quote" || k == K"inert" ||
           k == K"top" || k == K"core" || k == K"globalref" || k == K"outerref"
end

function is_single_assign_var(ctx::LinearIRContext, ex)
    return false # FIXME
    id = ex.var_id
    # return id in ctx.lambda_args ||
end

function is_const_read_arg(ctx, ex)
    k = kind(ex)
    return is_simple_atom(ctx, ex) ||
           is_single_assign_var(ctx, ex) ||
           k == K"quote" || k == K"inert" || k == K"top" || k == K"core"
end

function is_valid_ir_rvalue(ctx, lhs, rhs)
    return is_ssa(ctx, lhs) ||
           is_valid_ir_argument(ctx, rhs) ||
           (kind(lhs) == K"BindingId" &&
            # FIXME: add: splatnew isdefined invoke cfunction gc_preserve_begin copyast new_opaque_closure globalref outerref
            kind(rhs) in KSet"new call foreigncall")
end

# evaluate the arguments of a call, creating temporary locations as needed
function compile_args(ctx, args)
    # First check if all the arguments as simple (and therefore side-effect free).
    # Otherwise, we need to use ssa values for all arguments to ensure proper
    # left-to-right evaluation semantics.
    all_simple = all(a->is_simple_arg(ctx, a), args)
    args_out = SyntaxList(ctx)
    for arg in args
        arg_val = compile(ctx, arg, true, false)
        if (all_simple || is_const_read_arg(ctx, arg_val)) && is_valid_body_ir_argument(ctx, arg_val)
            push!(args_out, arg_val)
        else
            push!(args_out, emit_assign_tmp(ctx, arg_val))
        end
    end
    return args_out
end

function emit(ctx::LinearIRContext, ex)
    push!(ctx.code, ex)
    return ex
end

function emit(ctx::LinearIRContext, srcref, k, args...)
    emit(ctx, makenode(ctx, srcref, k, args...))
end

# Emit computation of ex, assigning the result to an ssavar and returning that
function emit_assign_tmp(ctx::LinearIRContext, ex, name="tmp")
    tmp = ssavar(ctx, ex, name)
    emit(ctx, @ast ctx ex [K"=" tmp ex])
    return tmp
end

function compile_pop_exception(ctx, srcref, src_tokens, dest_tokens)
    # It's valid to leave the context of src_tokens for the context of
    # dest_tokens when src_tokens is the same or nested within dest_tokens.
    # It's enough to check the token on the top of the dest stack.
    n = length(dest_tokens)
    jump_ok = n == 0 || (n <= length(src_tokens) && dest_tokens[n].var_id == src_tokens[n].var_id)
    jump_ok || throw(LoweringError(srcref, "Attempt to jump into catch block"))
    if n < length(src_tokens)
        @ast ctx srcref [K"pop_exception" src_tokens[n+1]]
    else
        nothing
    end
end

function compile_leave_handler(ctx, srcref, src_tokens, dest_tokens)
    n = length(dest_tokens)
    jump_ok = n == 0 || (n <= length(src_tokens) && dest_tokens[n].var_id == src_tokens[n].var_id)
    jump_ok || throw(LoweringError(srcref, "Attempt to jump into try block"))
    if n < length(src_tokens)
        @ast ctx srcref [K"leave" src_tokens[n+1:end]]
    else
        nothing
    end
end

function emit_pop_exception(ctx::LinearIRContext, srcref, dest_tokens)
    pexc = compile_pop_exception(ctx, srcref, ctx.catch_token_stack, dest_tokens)
    if !isnothing(pexc)
        emit(ctx, pexc)
    end
end

function emit_leave_handler(ctx::LinearIRContext, srcref, dest_tokens)
    ex = compile_leave_handler(ctx, srcref, ctx.handler_token_stack, dest_tokens)
    if !isnothing(ex)
        emit(ctx, ex)
    end
end

function emit_jump(ctx, srcref, target::JumpTarget)
    emit_pop_exception(ctx, srcref, target.catch_token_stack)
    emit_leave_handler(ctx, srcref, target.handler_token_stack)
    emit(ctx, @ast ctx srcref [K"goto" target.label])
end

# Enter the current finally block, either through the landing pad (on_exit ==
# :rethrow) or via a jump (on_exit ∈ (:return, :break)).
#
# An integer tag is created to identify the current code path and select the
# on_exit action to be taken at finally handler exit.
function enter_finally_block(ctx, srcref, on_exit, value)
    @assert on_exit ∈ (:rethrow, :break, :return)
    handler = last(ctx.finally_handlers)
    push!(handler.exit_actions, (on_exit, value))
    tag = length(handler.exit_actions)
    emit(ctx, @ast ctx srcref [K"=" handler.tagvar tag::K"Integer"])
    if on_exit != :rethrow
        emit_jump(ctx, srcref, handler.target)
    end
end

# Helper function for emit_return
function _actually_return(ctx, ex)
    # TODO: Handle the implicit return coverage hack for #53354 ?
    rett = ctx.return_type
    if !isnothing(rett)
        ex = compile(ctx, convert_for_type_decl(ctx, rett, ex, rett, true), true, false)
    end
    simple_ret_val = isempty(ctx.catch_token_stack) ?
        # returning lambda directly is needed for @generated
        (is_valid_ir_argument(ctx, ex) || kind(ex) == K"lambda") :
        is_simple_atom(ctx, ex)
    if !simple_ret_val
        ex = emit_assign_tmp(ctx, ex, "return_tmp")
    end
    emit_pop_exception(ctx, ex, ())
    emit(ctx, @ast ctx ex [K"return" ex])
    return nothing
end

function emit_return(ctx, srcref, ex)
    if isnothing(ex)
        return
    elseif isempty(ctx.handler_token_stack)
        _actually_return(ctx, ex)
        return
    end
    # FIXME: What's this !is_ssa(ctx, ex) here about?
    x = if is_simple_atom(ctx, ex) && !(is_ssa(ctx, ex) && !isempty(ctx.finally_handlers))
        ex
    elseif !isempty(ctx.finally_handlers)
        # TODO: Why does flisp lowering create a mutable variable here even
        # though we don't mutate it?
        # tmp = ssavar(ctx, srcref, "returnval_via_finally") # <- can we use this?
        tmp = new_mutable_var(ctx, srcref, "returnval_via_finally")
        emit(ctx, @ast ctx srcref [K"=" tmp ex])
        tmp
    else
        emit_assign_tmp(ctx, ex, "returnval_via_finally")
    end
    if !isempty(ctx.finally_handlers)
        enter_finally_block(ctx, srcref, :return, x)
    else
        emit(ctx, @ast ctx srcref [K"leave" ctx.handler_token_stack...])
        _actually_return(ctx, x)
    end
    # Should we return `x` here? The flisp code does, but that doesn't seem
    # useful as any returned value cannot be used?
    return nothing
end

function emit_return(ctx, ex)
    emit_return(ctx, ex, ex)
end

function emit_break(ctx, ex)
    name = ex[1].name_val
    target = get(ctx.break_targets, name, nothing)
    if isnothing(target)
        ty = name == "loop_exit" ? "break" : "continue"
        throw(LoweringError(ex, "$ty must be used inside a `while` or `for` loop"))
    end
    if !isempty(ctx.finally_handlers)
        handler = last(ctx.finally_handlers)
        if length(target.handler_token_stack) < length(handler.target.handler_token_stack)
            enter_finally_block(ctx, ex, :break, ex)
            return
        end
    end
    emit_jump(ctx, ex, target)
end

function emit_assignment(ctx, srcref, lhs, rhs)
    if !isnothing(rhs)
        if is_valid_ir_rvalue(ctx, lhs, rhs)
            emit(ctx, srcref, K"=", lhs, rhs)
        else
            r = emit_assign_tmp(ctx, rhs)
            emit(ctx, srcref, K"=", lhs, r)
        end
    else
        # in unreachable code (such as after return); still emit the assignment
        # so that the structure of those uses is preserved
        emit(ctx, @ast ctx srcref [K"=" lhs "nothing"::K"core"])
        nothing
    end
end

function make_label(ctx, srcref)
    id = ctx.next_label_id[]
    ctx.next_label_id[] += 1
    makeleaf(ctx, srcref, K"label", id=id)
end

# flisp: make&mark-label
function emit_label(ctx, srcref)
    if !isempty(ctx.code)
        # Use current label if available
        e = ctx.code[end]
        if kind(e) == K"label"
            return e
        end
    end
    l = make_label(ctx, srcref)
    emit(ctx, l)
    l
end

function compile_condition_term(ctx, ex)
    cond = compile(ctx, ex, true, false)
    if !is_valid_body_ir_argument(ctx, cond)
        cond = emit_assign_tmp(ctx, cond)
    end
    return cond
end

# flisp: emit-cond
function compile_conditional(ctx, ex, false_label)
    if kind(ex) == K"block"
        for i in 1:numchildren(ex)-1
            compile(ctx, ex[i], false, false)
        end
        test = ex[end]
    else
        test = ex
    end
    k = kind(test)
    if k == K"||"
        true_label = make_label(ctx, test)
        for (i,e) in enumerate(children(test))
            c = compile_condition_term(ctx, e)
            if i < numchildren(test)
                next_term_label = make_label(ctx, test)
                # Jump over short circuit
                emit(ctx, @ast ctx e [K"gotoifnot" c next_term_label])
                # Short circuit to true
                emit(ctx, @ast ctx e [K"goto" true_label])
                emit(ctx, next_term_label)
            else
                emit(ctx, @ast ctx e [K"gotoifnot" c false_label])
            end
        end
        emit(ctx, true_label)
    elseif k == K"&&"
        for e in children(test)
            c = compile_condition_term(ctx, e)
            emit(ctx, @ast ctx e [K"gotoifnot" c false_label])
        end
    else
        c = compile_condition_term(ctx, test)
        emit(ctx, @ast ctx test [K"gotoifnot" c false_label])
    end
end

function add_lambda_local!(ctx::LinearIRContext, id)
    push!(ctx.lambda_locals, id)
end

# Lowering of exception handling must ensure that
#
# * Each `enter` is matched with a `leave` on every possible non-exceptional
#   program path (including implicit returns generated in tail position).
# * Each catch block which is entered and handles the exception - by exiting
#   via a non-exceptional program path - leaves the block with `pop_exception`.
# * Each `finally` block runs, regardless of any early `return` or jumps
#   via `break`/`continue`/`goto` etc.
#
# These invariants are upheld by tracking the nesting using
# `handler_token_stack` and `catch_token_stack` and using these when emitting
# any control flow (return / goto) which leaves the associated block.
#
# The following special forms are emitted into the IR:
#
#   (= tok (enter catch_label dynscope))
#     push exception handler with catch block at `catch_label` and dynamic
#     scope `dynscope`, yielding a token which is used by `leave` and
#     `pop_exception`. `dynscope` is only used in the special `tryfinally` form
#     without associated source level syntax (see the `@with` macro)
#
#   (leave tok)
#     pop exception handler back to the state of the `tok` from the associated
#     `enter`. Multiple tokens can be supplied to pop multiple handlers using
#     `(leave tok1 tok2 ...)`.
#
#   (pop_exception tok) - pop exception stack back to state of associated enter
#
# See the devdocs for further discussion.
function compile_try(ctx::LinearIRContext, ex, needs_value, in_tail_pos)
    @chk numchildren(ex) <= 3
    try_block = ex[1]
    if kind(ex) == K"trycatchelse"
        catch_block = ex[2]
        else_block = numchildren(ex) == 2 ? nothing : ex[3]
        finally_block = nothing
        catch_label = make_label(ctx, catch_block)
    else
        catch_block = nothing
        else_block = nothing
        finally_block = ex[2]
        catch_label = make_label(ctx, finally_block)
    end

    end_label = !in_tail_pos || !isnothing(finally_block) ? make_label(ctx, ex) : nothing
    try_result = needs_value && !in_tail_pos ? new_mutable_var(ctx, ex, "try_result") : nothing

    # Exception handler block prefix
    handler_token = ssavar(ctx, ex, "handler_token")
    emit(ctx, @ast ctx ex [K"="
        handler_token
        [K"enter" catch_label]  # TODO: dynscope
    ])
    if !isnothing(finally_block)
        # TODO: Trivial finally block optimization from JuliaLang/julia#52593 (or
        # support a special form for @with)?
        finally_handler = FinallyHandler(new_mutable_var(ctx, finally_block, "finally_tag"),
                                         JumpTarget(end_label, ctx))
        push!(ctx.finally_handlers, finally_handler)
        emit(ctx, @ast ctx finally_block [K"=" finally_handler.tagvar -1::K"Integer"])
    end
    push!(ctx.handler_token_stack, handler_token)

    # Try block code.
    try_val = compile(ctx, try_block, needs_value, false)
    # Exception handler block postfix
    if isnothing(else_block)
        if in_tail_pos
            if !isnothing(try_val)
                emit_return(ctx, try_val)
            end
        else
            if needs_value && !isnothing(try_val)
                emit_assignment(ctx, ex, try_result, try_val)
            end
            emit(ctx, @ast ctx ex [K"leave" handler_token])
        end
        pop!(ctx.handler_token_stack)
    else
        if !isnothing(try_val) && (in_tail_pos || needs_value)
            emit(ctx, try_val) # TODO: Only for any side effects ?
        end
        emit(ctx, @ast ctx ex [K"leave" handler_token])
        pop!(ctx.handler_token_stack)
        # Else block code
        else_val = compile(ctx, else_block, needs_value, in_tail_pos)
        if !in_tail_pos
            if needs_value && !isnothing(else_val)
                emit_assignment(ctx, ex, try_result, else_val)
            end
        end
    end
    if !in_tail_pos
        emit(ctx, @ast ctx ex [K"goto" end_label])
    end

    # Catch pad
    # Emit either catch or finally block. A combined try/catch/finally block
    # was split into separate trycatchelse and tryfinally blocks earlier.
    emit(ctx, catch_label) # <- Exceptional control flow enters here
    if !isnothing(finally_block)
        # Attribute the postfix and prefix to the finally block as a whole.
        srcref = finally_block
        enter_finally_block(ctx, srcref, :rethrow, nothing)
        emit(ctx, end_label) # <- Non-exceptional control flow enters here
        pop!(ctx.finally_handlers)
        compile(ctx, finally_block, false, false)
        # Finally block postfix: Emit a branch for every code path which enters
        # the block to dynamically decide which return/break/rethrow exit action to take
        for (tag, (on_exit, value)) in Iterators.reverse(enumerate(finally_handler.exit_actions))
            next_action_label = !in_tail_pos || tag != 1 || on_exit != :return ?
                make_label(ctx, srcref) : nothing
            if !isnothing(next_action_label)
                next_action_label = make_label(ctx, srcref)
                tmp = ssavar(ctx, srcref, "do_finally_action")
                emit(ctx, @ast ctx srcref [K"=" tmp
                    [K"call"
                        "==="::K"core"
                        finally_handler.tagvar
                        tag::K"Integer"
                    ]
                ])
                emit(ctx, @ast ctx srcref [K"gotoifnot" tmp next_action_label])
            end
            if on_exit === :return
                emit_return(ctx, value)
            elseif on_exit === :break
                emit_break(ctx, value)
            elseif on_exit === :rethrow
                emit(ctx, @ast ctx srcref [K"call" "rethrow"::K"top"])
            else
                @assert false
            end
            if !isnothing(next_action_label)
                emit(ctx, next_action_label)
            end
        end
    else
        push!(ctx.catch_token_stack, handler_token)
        catch_val = compile(ctx, catch_block, needs_value, in_tail_pos)
        if !isnothing(try_result) && !isnothing(catch_val)
            emit_assignment(ctx, ex, try_result, catch_val)
        end
        if !in_tail_pos
            emit(ctx, @ast ctx ex [K"pop_exception" handler_token])
            emit(ctx, end_label)
        else
            # (pop_exception done in emit_return)
        end
        pop!(ctx.catch_token_stack)
    end
    try_result
end

# This pass behaves like an interpreter on the given code.
# To perform stateful operations, it calls `emit` to record that something
# needs to be done. In value position, it returns an expression computing
# the needed value.
function compile(ctx::LinearIRContext, ex, needs_value, in_tail_pos)
    k = kind(ex)
    if k == K"BindingId" || is_literal(k) || k == K"quote" || k == K"inert" ||
            k == K"top" || k == K"core" || k == K"Value" || k == K"Symbol" ||
            k == K"Placeholder"
        # TODO: other kinds: copyast $ globalref outerref thismodule cdecl stdcall fastcall thiscall llvmcall
        if needs_value && k == K"Placeholder"
            # TODO: ensure outterref, globalref work here
            throw(LoweringError(ex, "all-underscore identifiers are write-only and their values cannot be used in expressions"))
        end
        if in_tail_pos
            emit_return(ctx, ex)
        elseif needs_value
            ex
        else
            if k == K"BindingId" && !is_ssa(ctx, ex)
                emit(ctx, ex) # keep identifiers for undefined-var checking
            end
            nothing
        end
    elseif k == K"call"
        # TODO k ∈ splatnew foreigncall cfunction new_opaque_closure cglobal
        args = compile_args(ctx, children(ex))
        callex = makenode(ctx, ex, k, args)
        if in_tail_pos
            emit_return(ctx, ex, callex)
        elseif needs_value
            callex
        else
            emit(ctx, callex)
            nothing
        end
    elseif k == K"="
        lhs = ex[1]
        if kind(lhs) == K"Placeholder"
            compile(ctx, ex[2], needs_value, in_tail_pos)
        else
            rhs = compile(ctx, ex[2], true, false)
            # TODO look up arg-map for renaming if lhs was reassigned
            if needs_value && !isnothing(rhs)
                r = emit_assign_tmp(ctx, rhs)
                emit(ctx, ex, K"=", lhs, r)
                if in_tail_pos
                    emit_return(ctx, ex, r)
                else
                    r
                end
            else
                emit_assignment(ctx, ex, lhs, rhs)
            end
        end
    elseif k == K"block" || k == K"scope_block"
        nc = numchildren(ex)
        if nc == 0
            if in_tail_pos
                emit_return(ctx, nothing_(ctx, ex))
            elseif needs_value
                nothing_(ctx, ex)
            else
                nothing
            end
        else
            res = nothing
            for i in 1:nc
                islast = i == nc
                res = compile(ctx, ex[i], islast && needs_value, islast && in_tail_pos)
            end
            res
        end
    elseif k == K"break_block"
        end_label = make_label(ctx, ex)
        name = ex[1].name_val
        outer_target = get(ctx.break_targets, name, nothing)
        ctx.break_targets[name] = JumpTarget(end_label, ctx)
        compile(ctx, ex[2], false, false)
        if isnothing(outer_target)
            delete!(ctx.break_targets, name)
        else
            ctx.break_targets = outer_target
        end
        emit(ctx, end_label)
        if needs_value
            compile(ctx, nothing_(ctx, ex), needs_value, in_tail_pos)
        end
    elseif k == K"break"
        emit_break(ctx, ex)
    elseif k == K"symbolic_label"
        label = emit_label(ctx, ex)
        name = ex.name_val
        if haskey(ctx.symbolic_jump_targets, name)
            throw(LoweringError(ex, "Label `$name` defined multiple times"))
        end
        push!(ctx.symbolic_jump_targets, name=>JumpTarget(label, ctx))
        if in_tail_pos
            emit_return(ctx, ex, nothing_(ctx, ex))
        elseif needs_value
            throw(LoweringError(ex, "misplaced label in value position"))
        end
    elseif k == K"symbolic_goto"
        push!(ctx.symbolic_jump_origins, JumpOrigin(ex, length(ctx.code)+1, ctx))
        emit(ctx, makeleaf(ctx, ex, K"TOMBSTONE")) # ? pop_exception
        emit(ctx, makeleaf(ctx, ex, K"TOMBSTONE")) # ? leave
        emit(ctx, makeleaf(ctx, ex, K"TOMBSTONE")) # ? goto
        nothing
    elseif k == K"return"
        compile(ctx, ex[1], true, true)
        nothing
    elseif k == K"unnecessary"
        # `unnecessary` marks expressions generated by lowering that
        # do not need to be evaluated if their value is unused.
        if needs_value
            compile(ctx, ex[1], needs_value, in_tail_pos)
        else
            nothing
        end
    elseif k == K"TOMBSTONE"
        @chk !needs_value (ex,"TOMBSTONE encountered in value position")
        nothing
    elseif k == K"if" || k == K"elseif"
        @chk numchildren(ex) <= 3
        has_else = numchildren(ex) > 2
        else_label = make_label(ctx, ex)
        compile_conditional(ctx, ex[1], else_label)
        if in_tail_pos
            compile(ctx, ex[2], needs_value, in_tail_pos)
            emit(ctx, else_label)
            if has_else
                compile(ctx, ex[3], needs_value, in_tail_pos)
            else
                emit_return(ctx, ex, nothing_(ctx, ex))
            end
            nothing
        else
            val = needs_value && new_mutable_var(ctx, ex, "if_val")
            v1 = compile(ctx, ex[2], needs_value, in_tail_pos)
            if needs_value
                emit_assignment(ctx, ex, val, v1)
            end
            if has_else || needs_value
                end_label = make_label(ctx, ex)
                emit(ctx, @ast ctx ex [K"goto" end_label])
            else
                end_label = nothing
            end
            emit(ctx, else_label)
            v2 = if has_else
                compile(ctx, ex[3], needs_value, in_tail_pos)
            elseif needs_value
                nothing_(ctx, ex)
            end
            if needs_value
                emit_assignment(ctx, ex, val, v2)
            end
            if !isnothing(end_label)
                emit(ctx, end_label)
            end
            val
        end
    elseif k == K"trycatchelse" || k == K"tryfinally"
        compile_try(ctx, ex, needs_value, in_tail_pos)
    elseif k == K"method"
        # TODO
        # throw(LoweringError(ex,
        #     "Global method definition needs to be placed at the top level, or use `eval`"))
        if numchildren(ex) == 1
            if in_tail_pos
                emit_return(ctx, ex)
            elseif needs_value
                ex
            else
                emit(ctx, ex)
            end
        else
            @chk numchildren(ex) == 3
            fname = ex[1]
            sig = compile(ctx, ex[2], true, false)
            if !is_valid_ir_argument(ctx, sig)
                sig = emit_assign_tmp(ctx, sig)
            end
            lam = ex[3]
            if kind(lam) == K"lambda"
                lam = compile_lambda(ctx, lam)
            else
                # lam = emit_assign_tmp(ctx, compile(ctx, lam, true, false))
                TODO(lam, "non-lambda method argument??")
            end
            emit(ctx, ex, K"method", fname, sig, lam)
            @assert !needs_value && !in_tail_pos
            nothing
        end
    elseif k == K"lambda"
        lam = compile_lambda(ctx, ex)
        if in_tail_pos
            emit_return(ctx, lam)
        elseif needs_value
            lam
        else
            emit(ctx, lam)
        end
    elseif k == K"_while"
        end_label = make_label(ctx, ex)
        top_label = emit_label(ctx, ex)
        compile_conditional(ctx, ex[1], end_label)
        compile(ctx, ex[2], false, false)
        emit(ctx, @ast ctx ex [K"goto" top_label])
        emit(ctx, end_label)
        if needs_value
            compile(ctx, nothing_(ctx, ex), needs_value, in_tail_pos)
        end
    elseif k == K"_do_while"
        end_label = make_label(ctx, ex)
        top_label = emit_label(ctx, ex)
        compile(ctx, ex[1], false, false)
        compile_conditional(ctx, ex[2], end_label)
        emit(ctx, @ast ctx ex [K"goto" top_label])
        emit(ctx, end_label)
        if needs_value
            compile(ctx, nothing_(ctx, ex), needs_value, in_tail_pos)
        end
    elseif k == K"global"
        if needs_value
            throw(LoweringError(ex, "misplaced `global` declaration"))
        end
        emit(ctx, ex)
        nothing
    elseif k == K"local_def" || k == K"local"
        nothing
    else
        throw(LoweringError(ex, "Invalid syntax; $(repr(k))"))
    end
end

# flisp: compile-body
function compile_body(ctx, ex)
    compile(ctx, ex, true, true)

    # Fix up any symbolic gotos. (We can't do this earlier because the goto
    # might precede the label definition in unstructured control flow.)
    for origin in ctx.symbolic_jump_origins
        name = origin.goto.name_val
        target = get(ctx.symbolic_jump_targets, name, nothing)
        if isnothing(target)
            throw(LoweringError(origin.goto, "label `$name` referenced but not defined"))
        end
        i = origin.index
        pop_ex = compile_pop_exception(ctx, origin.goto, origin.catch_token_stack,
                                     target.catch_token_stack)
        if !isnothing(pop_ex)
            @assert kind(ctx.code[i]) == K"TOMBSTONE"
            ctx.code[i] = pop_ex
            i += 1
        end
        leave_ex = compile_leave_handler(ctx, origin.goto, origin.handler_token_stack,
                                         target.handler_token_stack)
        if !isnothing(leave_ex)
            @assert kind(ctx.code[i]) == K"TOMBSTONE"
            ctx.code[i] = leave_ex
            i += 1
        end
        @assert kind(ctx.code[i]) == K"TOMBSTONE"
        ctx.code[i] = @ast ctx origin.goto [K"goto" target.label]
    end
    # TODO: Filter out any newvar nodes where the arg is definitely initialized
end

#-------------------------------------------------------------------------------

# Recursively renumber an expression within linear IR
# flisp: renumber-stuff
function _renumber(ctx, ssa_rewrites, slot_rewrites, label_table, ex)
    k = kind(ex)
    if k == K"BindingId"
        id = ex.var_id
        if haskey(ssa_rewrites, id)
            makeleaf(ctx, ex, K"SSAValue"; var_id=ssa_rewrites[id])
        else
            slot_id = get(slot_rewrites, id, nothing)
            if !isnothing(slot_id)
                makeleaf(ctx, ex, K"slot"; var_id=slot_id)
            else
                # TODO: look up any static parameters
                # TODO: Should we defer rewriting globals to globalref until
                # CodeInfo generation?
                info = lookup_binding(ctx, id)
                if info.kind === :global
                    makeleaf(ctx, ex, K"globalref", info.name, mod=info.mod)
                else
                    TODO(ex, "Bindings of kind $(info.kind)")
                end
            end
        end
    elseif k == K"outerref" || k == K"meta"
        TODO(ex, "_renumber $k")
    elseif is_literal(k) || is_quoted(k)
        ex
    elseif k == K"label"
        @ast ctx ex label_table[ex.id]::K"label"
    elseif k == K"lambda"
        ex
    else
        mapchildren(ctx, ex) do e
            _renumber(ctx, ssa_rewrites, slot_rewrites, label_table, e)
        end
        # TODO: foreigncall error check:
        # "ccall function name and library expression cannot reference local variables"
    end
end

# flisp: renumber-lambda, compact-ir
function renumber_body(ctx, input_code, slot_rewrites)
    # Step 1: Remove any assignments to SSA variables, record the indices of labels
    ssa_rewrites = Dict{IdTag,IdTag}()
    label_table = Dict{Int,Int}()
    code = SyntaxList(ctx)
    for ex in input_code
        k = kind(ex)
        ex_out = nothing
        if k == K"=" && is_ssa(ctx, ex[1])
            lhs_id = ex[1].var_id
            if is_ssa(ctx, ex[2])
                # For SSA₁ = SSA₂, record that all uses of SSA₁ should be replaced by SSA₂
                ssa_rewrites[lhs_id] = ssa_rewrites[ex[2].var_id]
            else
                # Otherwise, record which `code` index this SSA value refers to
                ssa_rewrites[lhs_id] = length(code) + 1
                ex_out = ex[2]
            end
        elseif k == K"label"
            label_table[ex.id] = length(code) + 1
        elseif k == K"TOMBSTONE"
            # remove statement
        else
            ex_out = ex
        end
        if !isnothing(ex_out)
            push!(code, ex_out)
        end
    end

    # Step 2:
    # * Translate any SSA uses and labels into indices in the code table
    # * Translate locals into slot indices
    for i in 1:length(code)
        code[i] = _renumber(ctx, ssa_rewrites, slot_rewrites, label_table, code[i])
    end
    code
end

function _add_slots!(slot_rewrites, bindings, ids)
    n = length(slot_rewrites) + 1
    for id in ids
        info = lookup_binding(bindings, id)
        if info.kind == :local || info.kind == :argument
            slot_rewrites[id] = n
            n += 1
        end
    end
    slot_rewrites
end

function compile_lambda(outer_ctx, ex)
    info = ex.lambda_info
    # TODO: Add assignments for reassigned arguments to body using info.args
    ctx = LinearIRContext(outer_ctx, info.is_toplevel_thunk, ex.lambda_locals, info.ret_var)
    compile_body(ctx, ex[1])
    slot_rewrites = Dict{IdTag,Int}()
    _add_slots!(slot_rewrites, ctx.bindings, (arg.var_id for arg in info.args))
    # Sorting the lambda locals is required to remove dependence on Dict iteration order.
    _add_slots!(slot_rewrites, ctx.bindings, sort(collect(ex.lambda_locals)))
    # @info "" @ast ctx ex [K"block" ctx.code]
    code = renumber_body(ctx, ctx.code, slot_rewrites)
    makenode(ctx, ex, K"lambda",
             makenode(ctx, ex[1], K"block", code),
             lambda_info=info,
             slot_rewrites=slot_rewrites
            )
end

"""
This pass converts nested ASTs in the body of a lambda into a list of
statements (ie, Julia's linear/untyped IR).

Most of the compliexty of this pass is in lowering structured control flow (if,
loops, etc) to gotos and exception handling to enter/leave. We also convert
`K"BindingId"` into K"slot", `K"globalref"` or `K"SSAValue` as appropriate.
"""
function linearize_ir(ctx, ex)
    graph = ensure_attributes(ctx.graph,
                              slot_rewrites=Dict{IdTag,Int},
                              bindings=Bindings,
                              mod=Module,
                              id=Int)
    # TODO: Cleanup needed - `_ctx` is just a dummy context here. But currently
    # required to call reparent() ...
    GraphType = typeof(graph)
    _ctx = LinearIRContext(graph, SyntaxList(graph), ctx.bindings,
                           Ref(0), false, Set{IdTag}(), nothing,
                           Dict{String,JumpTarget{typeof(graph)}}(),
                           SyntaxList(graph), SyntaxList(graph),
                           Vector{FinallyHandler{GraphType}}(),
                           Dict{String, JumpTarget{GraphType}}(),
                           Vector{JumpOrigin{GraphType}}(), ctx.mod)
    res = compile_lambda(_ctx, reparent(_ctx, ex))
    setattr!(graph, res._id, bindings=ctx.bindings)
    _ctx, res
end

