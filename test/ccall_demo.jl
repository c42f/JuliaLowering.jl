module CCall

using JuliaSyntax, JuliaLowering
using JuliaLowering: is_identifier_like, numchildren, children, MacroExpansionError,
    @ast, SyntaxTree, @SyntaxTree

function ccall_macro_parse(ex)
    if kind(ex) != K"::"
        throw(MacroExpansionError(ex, "Expected a return type annotation like `::T`", position=:end))
    end

    rettype = ex[2]
    call = ex[1]
    if kind(call) != K"call"
        throw(MacroExpansionError(call, "Expected function call syntax `f()`"))
    end

    # get the function symbols
    func = let f = call[1], kf = kind(f)
        if kf == K"."
            @ast ex ex [K"tuple" f[2]=>K"Symbol" f[1]]
        elseif kf == K"$"
            f
        elseif kf == K"Identifier"
            @ast ex ex f=>K"Symbol"
        else
            throw(MacroExpansionError(f,
                "Function name must be a symbol like `foo`, a library and function name like `libc.printf` or an interpolated function pointer like `\$ptr`"))
        end
    end

    varargs = nothing

    # collect args and types
    args = SyntaxTree[]
    types = SyntaxTree[]

    function pusharg!(arg)
        if kind(arg) != K"::"
            throw(MacroExpansionError(arg, "argument needs a type annotation like `::T`"))
        end
        push!(args, arg[1])
        push!(types, arg[2])
    end

    varargs = nothing
    num_varargs = 0
    for e in call[2:end]
        if kind(e) == K"parameters"
            num_varargs == 0 || throw(MacroExpansionError(e, "Multiple parameter blocks not allowed"))
            num_varargs = numchildren(e)
            num_varargs > 0 || throw(MacroExpansionError(e, "C ABI prohibits vararg without one required argument"))
            varargs = children(e)
        else
            pusharg!(e)
        end
    end
    if !isnothing(varargs)
        for e in varargs
            pusharg!(e)
        end
    end

    return func, rettype, types, args, num_varargs
end

function ccall_macro_lower(ex, convention, func, rettype, types, args, num_varargs)
    statements = SyntaxTree[]
    if kind(func) == K"$"
        check = @SyntaxTree quote
            func = $(func[1])
            if !isa(func, Ptr{Cvoid})
                name = :($(func[1]))
                throw(ArgumentError("interpolated function `$name` was not a `Ptr{Cvoid}`, but $(typeof(func))"))
            end
        end
        func = check[1][1]
        push!(statements, check)
    end

    roots = SyntaxTree[]
    cargs = SyntaxTree[]
    for (i, (type, arg)) in enumerate(zip(types, args))
        argi = @ast ex arg "arg$i"::K"Identifier"
        # TODO: Can we allow this macro to emit SSAValue?
        push!(statements, @SyntaxTree :(local $argi = Base.cconvert($type, $arg)))
        push!(roots, argi)
        push!(cargs, @SyntaxTree :(Base.unsafe_convert($type, $argi)))
    end
    push!(statements,
          @ast ex ex [K"foreigncall"
              func
              rettype
              @SyntaxTree :(Core.svec($(types...)))
              # Is this num_varargs correct? It seems wrong?
              num_varargs::K"Integer"
              convention::K"Symbol"
              cargs...
              roots...
          ])

    @ast ex ex [K"block"
        statements...
    ]
end

function var"@ccall"(ctx::JuliaLowering.MacroContext, ex)
    ccall_macro_lower(ex, "ccall", ccall_macro_parse(ex)...)
end

end # module CCall
