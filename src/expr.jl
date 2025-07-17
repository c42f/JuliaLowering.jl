function is_eventually_call(ex)
    if ex isa Expr
        h = ex.head
        return h == :call || ((h == :where || h == :(::)) && is_eventually_call(ex.args[1]))
    else
        return false
    end
end

function _is_op_equals(h)
    return  h == :(+=)    || h == :(-=)    || h == :(*=)    || h == :(/=)    ||
            h == :(//=)   || h == :(\=)    || h == :(^=)    || h == :(÷=)    ||
            h == :(%=)    || h == :(<<=)   || h == :(>>=)   || h == :(>>>=)  ||
            h == :(|=)    || h == :(&=)    || h == :(⊻=)    || h == :(.+=)   ||
            h == :(.-=)   || h == :(.*=)   || h == :(./=)   || h == :(.//=)  ||
            h == :(.\=)   || h == :(.^=)   || h == :(.÷=)   || h == :(.%=)   ||
            h == :(.<<=)  || h == :(.>>=)  || h == :(.>>>=) || h == :(.|=)   ||
            h == :(.&=)   || h == :(.⊻=)   || h == :($=)
end

function _convert_macrocall_args(ex, curr_line)
    args = copy(ex.args)
    lno = splice!(args, 2)
    if lno isa LineNumberNode
        curr_line = lno
    end
    if args[1] isa GlobalRef && args[1].mod == Core
        macname = args[1].name
        if macname == Symbol("@int128_str")
            return K"Integer", nothing, Base.parse(Int128, args[2]), curr_line
        elseif macname == Symbol("@big_str")
            # TODO: Use K"BigInteger" and a string representation
            return K"Integer", nothing, Base.parse(BigInt, args[2]), curr_line
        elseif macname == Symbol("@uint128_str")
            str = args[2]
            k = startswith(str, "0b") ? K"BinInt" :
                startswith(str, "0o") ? K"OctInt" :
                startswith(str, "0x") ? K"HexInt" :
                @assert false
            return k, nothing, Base.parse(UInt128, str), curr_line
        elseif macname == Symbol("@cmd") && length(args) == 1
            popfirst!(args)
            # Note raw string is already unescaped in Expr format
            return K"cmdstring", args, nothing, curr_line
        elseif macname == Symbol("@doc") && length(args) == 2
            popfirst!(args)
            return K"doc", args, nothing, curr_line
        end
    end
    return K"macrocall", args, nothing, curr_line
end

function _expr_convert_leaf(graph::SyntaxGraph, ex, curr_line)
    id = newnode!(graph)
    if ex isa Symbol
        name = string(ex)
        if endswith(name, "_str")
            k = K"StringMacroName"
        elseif endswith(name, "_cmd")
            k = K"CmdMacroName"
        elseif startswith(name, "@")
            k = K"MacroName"
        elseif all(==('_'), name)
            k = K"Placeholder"
        else
            k = K"Identifier"
        end
        setattr!(graph, id, name_val=name)
    else
        if ex isa Int
            k = K"Integer"
        elseif ex isa Float64
            k = K"Float"
        elseif ex isa UInt8 || ex isa UInt16 || ex isa UInt32 || ex isa UInt64
            # For now we will assume these were all HexInt, but this is
            # somewhat semantically dubious after we've departed from the
            # source text representation - they could have been OctInt or
            # BinInt in the source and as Julia values the distinction is
            # meaningless anyway. Perhaps we should have K"UnsignedInteger"
            # for this use case?
            k = K"HexInt"
        elseif ex isa Float32
            k = K"Float32"
        elseif ex isa Bool
            k = K"Bool"
        elseif ex isa String
            k = K"String"
        elseif ex isa Char
            k = K"Char"
        else
            k = K"Value"
        end
        setattr!(graph, id, value=ex)
    end
    flags = JuliaSyntax.EMPTY_FLAGS
    sethead!(graph, id, JuliaSyntax.SyntaxHead(k, flags))
    setattr!(graph, id, source=curr_line)
    return id
end

function _expr_convert(graph::SyntaxGraph, ex, curr_line)
    flags = JuliaSyntax.EMPTY_FLAGS
    args = nothing
    if ex isa QuoteNode
        k = K"inert"
        args = Any[ex.value]
    elseif ex isa Expr
        h = ex.head
        if h == :scope_layer
            # Expect Expr(:escape, ex, scope_layer)
            @assert length(ex.args) == 2 && ex.args[2] isa LayerId && ex.args[1] isa Symbol
            id = _expr_convert_leaf(graph, ex.args[1], curr_line)
            setattr!(graph, id, scope_layer=ex.args[2])
            return id
        end
        k = h == :kw         ? K"="   :
            _is_op_equals(h) ? K"op=" :
                               Kind(string(h))
        args = ex.args
        if k == K"op="
            args = copy(args)
            opstr = string(h)
            has_dot = opstr[1] == '.'
            if has_dot
                flags |= JuliaSyntax.DOTOP_FLAG
            end
            opname = opstr[(has_dot ? 2 : 1):prevind(opstr, lastindex(opstr))]
            insert!(args, 2, Symbol(opname))
        elseif h == :. && length(args) == 2 && args[2] isa QuoteNode
            args = copy(args)
            args[2] = args[2].value
        elseif k == K"macrocall"
            k, args, val, curr_line = _convert_macrocall_args(ex, curr_line)
            if !isnothing(val)
                id = newnode!(graph)
                sethead!(graph, id, JuliaSyntax.SyntaxHead(k, flags))
                setattr!(graph, id, source=curr_line)
                setattr!(graph, id, value=val)
                return id
            end
        elseif k == K"call" && length(args) >= 2
            if Meta.isexpr(args[2], :parameters)
                push!(args, splice!(args, 2))
            end
        elseif k == K"=" && length(args) == 2 && is_eventually_call(args[1])
            k = K"function"
            flags |= JuliaSyntax.SHORT_FORM_FUNCTION_FLAG
        end
    else
        return _expr_convert_leaf(graph, ex, curr_line)
    end
    id = newnode!(graph)
    sethead!(graph, id, JuliaSyntax.SyntaxHead(k, flags))
    setattr!(graph, id, source=curr_line)
    if !isnothing(args)
        args::Vector{Any}
        cs = Vector{NodeId}()
        for arg in args
            if arg isa LineNumberNode
                curr_line = arg
            else
                push!(cs, _expr_convert(graph, arg, curr_line))
            end
        end
        if k == K"cmdstring" && length(cs) == 1
            setattr!(graph, cs[1], kind=K"CmdString")
        end
        setchildren!(graph, id, cs)
    end
    return id
end

function expr_to_SyntaxTree(graph::SyntaxGraph, ex, start_line=LineNumberNode(0))
    id = _expr_convert(graph, ex, start_line)
    return SyntaxTree(graph, id)
end

function expr_to_SyntaxTree(ex, start_line=LineNumberNode(0))
    graph = SyntaxGraph()
    ensure_attributes!(graph, kind=Kind, syntax_flags=UInt16, source=SourceAttrType,
                       value=Any, name_val=String)
    expr_to_SyntaxTree(freeze_attrs(graph), ex, start_line)
end

