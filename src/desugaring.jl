# Lowering Pass 2 - syntax desugaring 

struct LambdaInfo
    # TODO: Make SyntaxList concretely typed?
    args::SyntaxList
    static_parameters::SyntaxList
    ret_var::Union{Nothing,SyntaxTree}
    is_toplevel_thunk::Bool
end

struct DesugaringContext{GraphType} <: AbstractLoweringContext
    graph::GraphType
    next_var_id::Ref{VarId}
    scope_layers::Vector{ScopeLayer}
    mod::Module
end

function DesugaringContext(ctx)
    graph = ensure_attributes(syntax_graph(ctx),
                              kind=Kind, syntax_flags=UInt16,
                              source=SourceAttrType,
                              value=Any, name_val=String,
                              scope_type=Symbol, # :hard or :soft
                              var_id=VarId,
                              lambda_info=LambdaInfo)
    DesugaringContext(graph, ctx.next_var_id, ctx.scope_layers, ctx.current_layer.mod)
end

# Flatten nested && or || nodes and expand their children
function expand_cond_children(ctx, ex, cond_kind=kind(ex), flat_children=SyntaxList(ctx))
    for e in children(ex)
        if kind(e) == cond_kind
            expand_cond_children(ctx, e, cond_kind, flat_children)
        else
            push!(flat_children, expand_forms_2(ctx, e))
        end
    end
    flat_children
end

# Expand condition in, eg, `if` or `while`
function expand_condition(ctx, ex)
    isblock = kind(ex) == K"block"
    test = isblock ? ex[end] : ex
    k = kind(test)
    if k == K"&&" || k == K"||"
        # `||` and `&&` get special lowering so that they compile directly to
        # jumps rather than first computing a bool and then jumping.
        cs = expand_cond_children(ctx, test)
        @assert length(cs) > 1
        test = makenode(ctx, test, k, cs)
    else
        test = expand_forms_2(ctx, test)
    end
    if isblock
        # Special handling so that the rules for `&&` and `||` can be applied
        # to the last statement of a block
        @ast ctx ex [K"block" ex[1:end-1]... test]
    else
        test
    end
end

function expand_let(ctx, ex)
    scope_type = get(ex, :scope_type, :hard)
    blk = ex[2]
    if numchildren(ex[1]) == 0 # TODO: Want to use !haschildren(ex[1]) but this doesn't work...
        return @ast ctx ex [K"scope_block"(scope_type=scope_type) blk]
    end
    for binding in Iterators.reverse(children(ex[1]))
        kb = kind(binding)
        if is_sym_decl(kb)
            blk = @ast ctx ex [
                K"scope_block"(scope_type=scope_type)
                [K"local" binding]
                blk
            ]
        elseif kb == K"=" && numchildren(binding) == 2
            lhs = binding[1]
            rhs = binding[2]
            if is_sym_decl(lhs)
                blk = @ast ctx binding [
                    K"block"
                    tmp=rhs
                    [K"scope_block"(ex, scope_type=scope_type)
                        [K"local_def"(lhs) lhs] # TODO: Use K"local" with attr?
                        [K"="(rhs)
                            decl_var(lhs)
                            tmp
                        ]
                        blk
                    ]
                ]
            else
                TODO("Functions and multiple assignment")
            end
        else
            throw(LoweringError(binding, "Invalid binding in let"))
            continue
        end
    end
    return blk
end

# Wrap unsplatted arguments in `tuple`:
# `[a, b, xs..., c]` -> `[(a, b), xs, (c,)]`
function _wrap_unsplatted_args(ctx, call_ex, args)
    wrapped = SyntaxList(ctx)
    i = 1
    while i <= length(args)
        if kind(args[i]) == K"..."
            splatarg = args[i]
            @chk numchildren(splatarg) == 1
            push!(wrapped, splatarg[1])
        else
            i1 = i
            # Find range of non-splatted args
            while i < length(args) && kind(args[i+1]) != K"..."
                i += 1
            end
            push!(wrapped, @ast ctx call_ex [K"call" "tuple"::K"core" args[i1:i]...])
        end
        i += 1
    end
    wrapped
end

function expand_call(ctx, ex)
    cs = children(ex)
    if is_infix_op_call(ex)
        @chk numchildren(ex) == 3
        cs = [cs[2], cs[1], cs[3]]
    elseif is_postfix_op_call(ex)
        @chk numchildren(ex) == 2
        cs = [cs[2], cs[1]]
    end
    # TODO: keywords
    if any(kind(c) == K"..." for c in cs)
        # Splatting, eg, `f(a, xs..., b)`
        @ast ctx ex [K"call" 
            "_apply_iterate"::K"core"
            "iterate"::K"top"
            expand_forms_2(ctx, cs[1])
            expand_forms_2(ctx, _wrap_unsplatted_args(ctx, ex, cs[2:end]))...
        ]
    else
        @ast ctx ex [K"call" expand_forms_2(ctx, cs)...]
    end
end

# Strip variable type declarations from within a `local` or `global`, returning
# the stripped expression. Works recursively with complex left hand side
# assignments containing tuple destructuring. Eg, given
#   (x::T, (y::U, z))
#   strip out stmts = (local x) (decl x T) (local x) (decl y U) (local z)
#   and return (x, (y, z))
function strip_decls!(ctx, stmts, declkind, ex)
    k = kind(ex)
    if k == K"Identifier"
        push!(stmts, makenode(ctx, ex, declkind, ex))
        ex
    elseif k == K"::"
        @chk numchildren(ex) == 2
        name = ex[1]
        @chk kind(name) == K"Identifier"
        push!(stmts, makenode(ctx, ex, declkind, name))
        push!(stmts, makenode(ctx, ex, K"decl", name, ex[2]))
        name
    elseif k == K"tuple" || k == K"parameters"
        cs = SyntaxList(ctx)
        for e in children(ex)
            push!(cs, strip_decls!(ctx, stmts, declkind, e))
        end
        makenode(ctx, ex, k, cs)
    end
end

# local x, (y=2), z => local x; local y; y = 2; local z
function expand_decls(ctx, ex)
    declkind = kind(ex)
    stmts = SyntaxList(ctx)
    for binding in children(ex)
        kb = kind(binding)
        if is_function_def(binding)
            push!(stmts, makenode(ctx, binding, declkind, assigned_name(binding)))
            push!(stmts, binding)
        elseif is_prec_assignment(kb)
            lhs = strip_decls!(ctx, stmts, declkind, binding[1])
            push!(stmts, makenode(ctx, binding, kb, lhs, binding[2]))
        elseif is_sym_decl(binding)
            strip_decls!(ctx, stmts, declkind, binding)
        else
            throw(LoweringError("invalid syntax in variable declaration"))
        end
    end
    makenode(ctx, ex, K"block", stmts)
end

function analyze_function_arg(full_ex)
    name = nothing
    type = nothing
    default = nothing
    is_slurp = false
    is_nospecialize = false
    ex = full_ex
    while true
        k = kind(ex)
        if k == K"Identifier" || k == K"Placeholder" || k == K"tuple"
            name = ex
            break
        elseif k == K"::"
            @chk numchildren(ex) in (1,2)
            if numchildren(ex) == 1
                type = ex[1]
            else
                name = ex[1]
                type = ex[2]
            end
            break
        elseif k == K"..."
            @chk !is_slurp (full_ex,"nested `...` in function argument")
            @chk numchildren(ex) == 1
            is_slurp = true
            ex = ex[1]
        elseif k == K"meta"
            @chk ex[1].name_val == "nospecialize"
            is_nospecialize = true
            ex = ex[2]
        elseif k == K"="
            @chk full_ex isnothing(default) && !is_slurp
            default = ex[2]
            ex = ex[1]
        else
            throw(LoweringError(ex, "Invalid function argument"))
        end
    end
    return (name=name,
            type=type,
            default=default,
            is_slurp=is_slurp,
            is_nospecialize=is_nospecialize)
end

function expand_function_def(ctx, ex, docs)
    @chk numchildren(ex) in (1,2)
    name = ex[1]
    if kind(name) == K"where"
        TODO("where handling")
    end
    return_type = nothing
    if kind(name) == K"::"
        @chk numchildren(name) == 2
        return_type = name[2]
        name = name[1]
    end
    if numchildren(ex) == 1 && is_identifier(name) # TODO: Or name as globalref
        if !is_valid_name(name)
            throw(LoweringError(name, "Invalid function name"))
        end
        return @ast ctx ex [K"method" name]
    elseif kind(name) == K"call"
        callex = name
        body = ex[2]
        # TODO
        # static params
        # nospecialize
        # argument destructuring
        # dotop names
        # overlays
        static_parameters = SyntaxList(ctx)

        # Add self argument where necessary
        args = name[2:end]
        name = name[1]
        if kind(name) == K"::"
            if numchildren(name) == 1
                farg = @ast ctx name [K"::"
                    "#self#"::K"Identifier"
                    name[1]
                ]
            else
                TODO("Fixme type")
                farg = name
            end
            function_name = nothing_(ctx, ex)
        else
            if !is_valid_name(name)
                throw(LoweringError(name, "Invalid function name"))
            end
            farg = @ast ctx name [K"::"
                "#self#"::K"Identifier"
                [K"call"
                    "Typeof"::K"core"
                    name
                ]
            ]
            function_name = name
        end
        args = pushfirst!(collect(args), farg)

        # preamble is arbitrary code which computes
        # svec(types, sparms, location)

        arg_names = SyntaxList(ctx)
        arg_types = SyntaxList(ctx)
        for (i,arg) in enumerate(args)
            info = analyze_function_arg(arg)
            aname = (isnothing(info.name) || kind(info.name) == K"Placeholder") ?
                    unused(ctx, arg) : info.name
            push!(arg_names, aname)
            atype = !isnothing(info.type) ? info.type : Any_type(ctx, arg)
            @assert !info.is_nospecialize # TODO
            @assert !isnothing(info.name) && kind(info.name) == K"Identifier" # TODO
            if info.is_slurp
                if i != length(args)
                    throw(LoweringError(arg, "`...` may only be used for the last function argument"))
                end
                atype = @ast ctx arg [K"curly" "Vararg"::K"core" arg]
            end
            push!(arg_types, atype)
        end

        preamble = @ast ctx callex [
            K"call"
            "svec"              ::K"core"
            [K"call"
                "svec"          ::K"core"
                arg_types...
            ]
            [K"call"
                "svec"          ::K"core"
                # FIXME sparams
            ]
            QuoteNode(source_location(LineNumberNode, callex))::K"Value"
        ]
        if !isnothing(return_type)
            body = @ast ctx body [
                K"block"
                ret_var=return_type
                body
            ]
        else
            ret_var = nothing
        end
        @ast ctx ex [
            K"block"
            func = [K"method" function_name]
            [K"method"
                function_name
                preamble
                [K"lambda"(body, lambda_info=LambdaInfo(arg_names, static_parameters, ret_var, false))
                    body
                ]
            ]
            if !isnothing(docs)
                [K"call"(docs)
                    bind_docs!::K"Value"
                    func
                    docs[1]
                    method_metadata
                ]
            end
            [K"unnecessary" func]
        ]
    elseif kind(name) == K"tuple"
        TODO(name, "Anon function lowering")
    else
        throw(LoweringError(name, "Bad function definition"))
    end
end

function _make_macro_name(ctx, name)
    @chk kind(name) == K"Identifier" (name, "invalid macro name")
    ex = mapleaf(ctx, name, K"Identifier")
    ex.name_val = "@$(name.name_val)"
    ex
end

# flisp: expand-macro-def
function expand_macro_def(ctx, ex)
    @chk numchildren(ex) >= 1 (ex,"invalid macro definition")
    if numchildren(ex) == 1
        name = ex[1]
        # macro with zero methods
        # `macro m end`
        return @ast ctx ex [K"function" _make_macro_name(ctx, name)]
    end
    # TODO: Making this manual pattern matching robust is such a pain!!!
    sig = ex[1]
    @chk (kind(sig) == K"call" && numchildren(sig) >= 1) (sig, "invalid macro signature")
    name = sig[1]
    args = remove_empty_parameters(children(sig))
    @chk kind(args[end]) != K"parameters" (args[end], "macros cannot accept keyword arguments")
    ret = @ast ctx ex [K"function"
        [K"call"(sig)
            _make_macro_name(ctx, name)
            [K"::"
                adopt_scope(@ast(ctx, sig, "__context__"::K"Identifier"), name)
                MacroContext::K"Value"
            ]
            # flisp: We don't mark these @nospecialize because all arguments to
            # new macros will be of type SyntaxTree
            args[2:end]...
        ]
        ex[2]
    ]
end

function _append_importpath(ctx, path_spec, path)
    prev_was_dot = true
    for component in children(path)
        k = kind(component)
        if k == K"quote"
            # Permit quoted path components as in
            # import A.(:b).:c
            component = component[1]
        end
        @chk kind(component) in (K"Identifier", K".")
        name = component.name_val
        is_dot = kind(component) == K"."
        if is_dot && !prev_was_dot
            throw(LoweringError(component, "invalid import path: `.` in identifier path"))
        end
        prev_was_dot = is_dot
        push!(path_spec, @ast(ctx, component, name::K"String"))
    end
    path_spec
end

function expand_import(ctx, ex)
    is_using = kind(ex) == K"using"
    if kind(ex[1]) == K":"
        # import M: x.y as z, w
        # (import (: (importpath M) (as (importpath x y) z) (importpath w)))
        # =>
        # (call module_import
        #  false
        #  (call core.svec "M")
        #  (call core.svec  2 "x" "y" "z"  1 "w" "w"))
        @chk numchildren(ex[1]) >= 2
        from = ex[1][1]
        @chk kind(from) == K"importpath"
        from_path = @ast ctx from [K"call"
            "svec"::K"core"
            _append_importpath(ctx, SyntaxList(ctx), from)...
        ]
        paths = ex[1][2:end]
    else
        # import A.B
        # (using (importpath A B))
        # (call module_import true nothing (call core.svec 1 "w"))
        @chk numchildren(ex) >= 1
        from_path = nothing_(ctx, ex)
        paths = children(ex)
    end
    path_spec = SyntaxList(ctx)
    for path in paths
        as_name = nothing
        if kind(path) == K"as"
            @chk numchildren(path) == 2
            as_name = path[2]
            @chk kind(as_name) == K"Identifier"
            path = path[1]
        end
        @chk kind(path) == K"importpath"
        push!(path_spec, @ast(ctx, path, numchildren(path)::K"Integer"))
        _append_importpath(ctx, path_spec, path)
        push!(path_spec, isnothing(as_name) ? nothing_(ctx, ex) :
                         @ast(ctx, as_name, as_name.name_val::K"String"))
    end
    @ast ctx ex [
        K"call"
        module_import ::K"Value"
        ctx.mod       ::K"Value"
        is_using      ::K"Value"
        from_path
        [K"call"
            "svec"::K"core"
            path_spec...
        ]
    ]
end

function expand_module(ctx::DesugaringContext, ex::SyntaxTree)
    modname_ex = ex[1]
    @chk kind(modname_ex) == K"Identifier"
    modname = modname_ex.name_val

    std_defs = if !has_flags(ex, JuliaSyntax.BARE_MODULE_FLAG)
        @ast ctx (@HERE) [
            K"block"
            [K"using"(@HERE)
                [K"importpath"
                    "Base"           ::K"Identifier"
                ]
            ]
            [K"function"(@HERE)
                [K"call"
                    "eval"           ::K"Identifier"
                    "x"              ::K"Identifier"
                ]
                [K"call"
                    "eval"           ::K"core"      
                    modname          ::K"Identifier"
                    "x"              ::K"Identifier"
                ]
            ]
            [K"function"(@HERE)
                [K"call"
                    "include"        ::K"Identifier"
                    "x"              ::K"Identifier"
                ]
                [K"call"
                    "_call_latest"   ::K"core"
                    "include"        ::K"top"
                    modname          ::K"Identifier"
                    "x"              ::K"Identifier"
                ]
            ]
            [K"function"(@HERE)
                [K"call"
                    "include"        ::K"Identifier"
                    [K"::"
                        "mapexpr"    ::K"Identifier"
                        "Function"   ::K"top"
                    ]
                    "x"              ::K"Identifier"
                ]
                [K"call"
                    "_call_latest"   ::K"core" 
                    "include"        ::K"top" 
                    "mapexpr"        ::K"Identifier" 
                    modname          ::K"Identifier" 
                    "x"              ::K"Identifier" 
                ]
            ]
        ]
    end

    body = ex[2]
    @chk kind(body) == K"block"

    @ast ctx ex [
        K"call"
        eval_module ::K"Value"
        ctx.mod     ::K"Value"
        modname     ::K"String"
        [K"inert"(body)
            [K"toplevel"
                std_defs
                children(body)...
            ]
        ]
    ]
end

"""
Lowering pass 2 - desugaring

This pass simplifies expressions by expanding complicated syntax sugar into a
small set of core syntactic forms. For example, field access syntax `a.b` is
expanded to a function call `getproperty(a, :b)`.
"""
function expand_forms_2(ctx::DesugaringContext, ex::SyntaxTree, docs=nothing)
    k = kind(ex)
    if k == K"call"
        expand_call(ctx, ex)
    elseif k == K"."
        @chk numchildren(ex) == 2
        @chk kind(ex[2]) == K"Identifier"
        expand_forms_2(ctx,
            @ast ctx ex [K"call"
                "getproperty"::K"top" 
                ex[1]
                ex[2]=>K"Symbol"
            ]
        )
    elseif k == K"?"
        @chk numchildren(ex) == 3
        expand_forms_2(ctx, @ast ctx ex [K"if" children(ex)...])
    elseif k == K"&&" || k == K"||"
        @chk numchildren(ex) > 1
        cs = expand_cond_children(ctx, ex)
        # Attributing correct provenance for `cs[1:end-1]` is tricky in cases
        # like `a && (b && c)` because the expression constructed here arises
        # from the source fragment `a && (b` which doesn't follow the tree
        # structure. For now we attribute to the parent node.
        cond = length(cs) == 2 ?
            cs[1] :
            makenode(ctx, ex, k, cs[1:end-1])
        # This transformation assumes the type assertion `cond::Bool` will be
        # added by a later pass.
        if k == K"&&"
            @ast ctx ex [K"if" cond cs[end] false::K"Bool"]
        else
            @ast ctx ex [K"if" cond true::K"Bool" cs[end]]
        end
    elseif k == K"break"
        numchildren(ex) > 0 ? ex :
            @ast ctx ex [K"break" "loop_exit"::K"symbolic_label"]
    elseif k == K"continue"
        @ast ctx ex [K"break" "loop_cont"::K"symbolic_label"]
    elseif k == K"doc"
        @chk numchildren(ex) == 2
        sig = expand_forms_2(ctx, ex[2], ex)
    elseif k == K"function"
        expand_forms_2(ctx, expand_function_def(ctx, ex, docs))
    elseif k == K"macro"
        expand_forms_2(ctx, expand_macro_def(ctx, ex))
    elseif k == K"if" || k == K"elseif"
        @chk numchildren(ex) >= 2
        @ast ctx ex [k
            expand_condition(ctx, ex[1])
            expand_forms_2(ctx, ex[2:end])...
        ]
    elseif k == K"let"
        expand_forms_2(ctx, expand_let(ctx, ex))
    elseif k == K"local" || k == K"global"
        if numchildren(ex) == 1 && kind(ex[1]) == K"Identifier"
            # Don't recurse when already simplified - `local x`, etc
            ex
        else
            expand_forms_2(ctx, expand_decls(ctx, ex)) # FIXME
        end
    elseif is_operator(k) && !haschildren(ex)
        makeleaf(ctx, ex, K"Identifier", ex.name_val)
    elseif k == K"char" || k == K"var"
        @chk numchildren(ex) == 1
        ex[1]
    elseif k == K"string"
        if numchildren(ex) == 1 && kind(ex[1]) == K"String"
            ex[1]
        else
            @ast ctx ex [K"call" 
                "string"::K"top"
                expand_forms_2(ctx, children(ex))...
            ]
        end
    elseif k == K"tuple"
        # TODO: named tuples
        expand_forms_2(ctx, @ast ctx ex [K"call" 
            "tuple"::K"core"
            children(ex)...
        ])
    elseif k == K"$"
        throw(LoweringError(ex, "`\$` expression outside quote"))
    elseif k == K"module"
        # TODO: check-toplevel
        expand_module(ctx, ex)
    elseif k == K"import" || k == K"using"
        # TODO: check-toplevel
        expand_import(ctx, ex)
    elseif k == K"export" || k == K"public"
        TODO(ex)
    elseif k == K"ref"
        if numchildren(ex) > 2
            TODO(ex, "ref expansion")
        end
        expand_forms_2(ctx, @ast ctx ex [K"call" "getindex"::K"top" ex[1] ex[2]])
    elseif k == K"toplevel"
        # The toplevel form can't be lowered here - it needs to just be quoted
        # and passed through to a call to eval.
        # TODO: check-toplevel
        @ast ctx ex [
            K"call"
            eval          ::K"Value"
            ctx.mod       ::K"Value"
            [K"inert" ex]
        ]
    elseif k == K"vect"
        @ast ctx ex [K"call"
            "vect"::K"top"
            expand_forms_2(ctx, children(ex))...
        ]
    elseif k == K"while"
        @chk numchildren(ex) == 2
        @ast ctx ex [K"break_block" "loop_exit"::K"symbolic_label"
            [K"_while"
                expand_condition(ctx, ex[1])
                [K"break_block" "loop_cont"::K"symbolic_label"
                    [K"scope_block"(scope_type=:neutral)
                         expand_forms_2(ctx, ex[2])
                    ]
                ]
            ]
        ]
    elseif k == K"inert"
        ex
    elseif !haschildren(ex)
        ex
    else
        if k == K"="
            @chk numchildren(ex) == 2
            if kind(ex[1]) ∉ KSet"Identifier Placeholder SSAValue"
                TODO(ex, "destructuring assignment")
            end
        end
        mapchildren(e->expand_forms_2(ctx,e), ctx, ex)
    end
end

function expand_forms_2(ctx::DesugaringContext, exs::Union{Tuple,AbstractVector})
    res = SyntaxList(ctx)
    for e in exs
        push!(res, expand_forms_2(ctx, e))
    end
    res
end

function expand_forms_2(ctx, ex::SyntaxTree)
    ctx1 = DesugaringContext(ctx)
    ex1 = expand_forms_2(ctx1, reparent(ctx1, ex))
    ctx1, ex1
end

