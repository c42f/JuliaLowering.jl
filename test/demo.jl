# Just some hacking

using JuliaSyntax
using JuliaLowering

using JuliaLowering: SyntaxGraph, SyntaxTree, ensure_attributes!, ensure_attributes, newnode!, setchildren!, is_leaf, children, child, setattr!, sourceref, makenode, sourcetext, showprov, lookup_binding

using JuliaSyntaxFormatter

# Extract variable kind for highlighting purposes
function var_kind(ctx, ex)
    id = get(ex, :var_id, nothing)
    if isnothing(id)
        return nothing
    end
    return lookup_binding(ctx, id).kind
end

# Extract module of globals for highlighting
function var_mod(ctx, ex)
    id = get(ex, :var_id, nothing)
    if isnothing(id)
        return nothing
    end
    return lookup_binding(ctx, id).mod
end

function formatsrc(ex; kws...)
    Text(JuliaSyntaxFormatter.formatsrc(ex; kws...))
end

# Currently broken - need to push info back onto src
# function annotate_scopes(mod, ex)
#     ex = ensure_attributes(ex, var_id=Int)
#     ctx1, ex_macroexpand = JuliaLowering.expand_forms_1(mod, ex)
#     ctx2, ex_desugar = JuliaLowering.expand_forms_2(ctx1, ex_macroexpand)
#     ctx3, ex_scoped = JuliaLowering.resolve_scopes(ctx2, ex_desugar)
#     ex
# end

#-------------------------------------------------------------------------------
# Module containing macros used in the demo.
baremodule M
    using Base

    using JuliaLowering: JuliaLowering, @ast, @chk, adopt_scope, MacroExpansionError, makenode
    using JuliaSyntax

    macro K_str(str)
        convert(JuliaSyntax.Kind, str)
    end

    function var"@inert"(__context__::JuliaLowering.MacroContext, ex)
        @chk kind(ex) == K"quote"
        @ast __context__ ex [K"inert" ex]
    end

    function var"@label"(__context__::JuliaLowering.MacroContext, ex)
        @chk kind(ex) == K"Identifier"
        @ast __context__ ex ex=>K"symbolic_label"
    end

    function var"@goto"(__context__::JuliaLowering.MacroContext, ex)
        @chk kind(ex) == K"Identifier"
        @ast __context__ ex ex=>K"symbolic_goto"
    end

    function var"@islocal"(__context__::JuliaLowering.MacroContext, ex)
        @chk kind(ex) == K"Identifier"
        @ast __context__ ex [K"extension"
            "islocal"::K"Symbol"
            ex
        ]
    end

    function var"@locals"(__context__::JuliaLowering.MacroContext)
        @ast __context__ __context__.macroname [K"extension" "locals"::K"Symbol"]
    end

    # JuliaLowering.include(M, "demo_include.jl")
end

#-------------------------------------------------------------------------------
# Demos of the prototype

# src = """
# let
#     local x, (y = 2), (w::T = ww), q::S
# end
# """

# src = """
# function foo(x::f(T), y::w(let ; S end))
#     "a \$("b \$("c")")"
# end
# """

src = """
begin
    function f(x)
        nothing
    end

    f(1)
end
"""

# src = """
#     x + y
# """

# src = """
# module A
#     function f(x)::Int
#         x + 1
#     end
#
#     b = f(2)
# end
# """

# src = """
# function f()
# end
# """
#
# src = """
# # import A.B: C.c as d, E.e as f
# # import JuliaLowering
# using JuliaLowering
# """
#
# src = """
# module A
#     z = 1 + 1
# end
# """

src = raw"""
begin
    x = 10
    y = :(g(z))
    quote
        f($(x+1), $y)
    end
end
"""

function wrapscope(ex, scope_type)
    makenode(ex, ex, K"scope_block", ex; scope_type=scope_type)
end

function softscope_test(ex)
    g = ensure_attributes(ex._graph, scope_type=Symbol)
    wrapscope(wrapscope(JuliaLowering.reparent(g, ex), :neutral), :soft)
end

# src = """
# M.@test_inert_quote()
# """

# src = """
# macro mmm(a; b=2)
# end
# macro A.b(ex)
# end
# """

# src = """
# M.@set_global_in_parent "bent hygiene!"
# """

# src = """
# begin
# M.@__LINE__
# end
# """

# src = """@foo z"""

src = """
M.@recursive 3
"""

# src = """
# M.@set_global_in_parent "bent hygiene!"
# """

# src = """
# begin
#    x = 10
#    y = 20
#    let x = y + x
#        z = "some string \$x \$y"
#
#        function f(y)
#            a = M.@foo z
#            "\$z \$y \$a \$x"
#        end
#        print(x)
#    end
#    print(x)
# end
# """

# src = """
# begin
#     x = -1
#     M.@baz x
# end
# """

# src = """
#     _ = -1
# """

# src = """
# M.@make_module
# """

# src = """
# M.@nested_return_a_value
# """

# src = """
# function f(y)
#     x = 42 + y
#     M.@foo error(x)
# end
# """

src = """
let
    y = 0
    x = 1
    let x = x + 1
        y = x
    end
    (x, y)
end
"""

#src = """M.@outer"""

src = """
begin
    local a, b, c
    if a
        b
    else
        c
    end
end
"""

src = """
begin
    local i = 0
    while i < 10
        i = i + 1
        if isodd(i)
            continue
        end
        println(i)
    end
end
"""

src = """
for i in [3,1,2]
    println("i = ", i, ", j = ", j)
end
"""

# src = """
# @ccall f()::T
# """
#
# src = """
# begin
#     a = 1
#     xs = [:(a),]
#     x = :(:(\$(\$(xs...))))
# end
# """

# src = """
# try
#     a
# catch exc
#     b
# end
# """

src = """
let
    a = []
    for i = 1:2, j = 3:4
        push!(a, (i,j))
        i = 100
    end
    a
end
"""

src = """
begin
    function f(x)
        y = x + 1
        "hi", x, y
    end

    f(1)
end
"""

src = """
let
    x = try
        error("hi")
        1
    catch exc
        current_exceptions()
    else
        3
    end
    x
end
"""

src = """
function f(y)
    x = 
    try
        try
            error("hi")
            1
        catch exc
            if y
                return 2
            end
            3
        else
            4
        end
    catch
        5
    end
    x
end
"""

src = """
function f(x)::Int
    if x
        42.0
    end
    0xff
end
"""

src = """
let x = 10
    global a = []
    try
        try
            return 100
        finally
            push!(a, 1)
        end
    finally
        push!(a, 2)
    end
    x
end
"""

src = """
let
    for outer i = 1:2
        body
    end
end
"""

src = """
let
    i = "hi"
    j = 1
    M.@label foo
    try
        println("i = ", i)
        i = i + 1
        if i <= 2
            M.@goto foo
        end
    catch exc
        println("Caught exception ", exc)
        j = j + 1
        if j <= 2
            println("Trying again ", exc)
            M.@goto foo
        end
    end
end
"""

src = """
let
    M.@goto foo
    M.@label foo
end
"""

src = """
x = M.@label foo
"""

src = """
begin
    local x::T = 1
    local x::S = 1
end
"""

src = """
begin
    local a, b
    if a
        b
    end
end
"""

src = """
let
    A{S} = B{S}
end
"""

src = """
let
    a = b = c = sin(1)
    (a,b,c)
end
"""

src = """
a.b = c
"""

src = """
a[i j] = c
"""

src = """
let
    as = [1,2,3,4]
    (x,ys...,z) = as
    (x,ys,z)
end
"""

src = """
let
    x = (1,2)
    (y,x) = x
    (x,y)
end
"""

src = """
let
    a = b = c = sin(1)
    (a,b,c)
end
"""

src = """
begin
    as = [(1,2), (3,4)]
    ((x,y), (z,w)) = as
end
"""

src = """
let
(x, y) = (y,x)
end
"""

src = """
let x = 1
    M.@islocal x
end
"""

src = """
let x = 1
    local y
    M.@locals
end
"""

src = """
let
    (a, bs...,) = (1,2,3)
    bs
end
"""

src = """
(; a=1, a=2)
"""

function f(args...; kws...)
    @info "" args kws
end

src = """
begin
    kws = (c=3, d=4)
    xs = 1:3
    f(xs...; kws..., a=1, b=2)
end
"""

src = """
"some docs"
function f()
    println("hi")
end
"""

src = """
function f(::T, ::U, ::S) where T where {U,S}
    println(T)
    println(U)
    println(S)
end
"""

src = """
function (x::XXX)(y)
    println("hi", " ", x, " ", y)
end
"""

src = """
struct X
    x
    y::String
end
"""

src = """
struct X{U,V}
    x::U
    y::V
end
"""

src = """
struct S9{T}
    x
    y

    "Docs for S9"
    S9{Int}(xs) = new(xs...)
end
"""

ex = parsestmt(SyntaxTree, src, filename="foo.jl")
ex = ensure_attributes(ex, var_id=Int)
#ex = softscope_test(ex)
@info "Input code" formatsrc(ex)

module MMM end
in_mod = MMM
# in_mod=Main
ctx1, ex_macroexpand = JuliaLowering.expand_forms_1(in_mod, ex)
@info "Macro expanded" ex_macroexpand formatsrc(ex_macroexpand, color_by=:scope_layer)
#@info "Macro expanded" formatsrc(ex_macroexpand, color_by=e->JuliaLowering.flattened_provenance(e)[1:end-1])

ctx2, ex_desugar = JuliaLowering.expand_forms_2(ctx1, ex_macroexpand)
@info "Desugared" ex_desugar formatsrc(ex_desugar, color_by=:scope_layer)

ctx3, ex_scoped = JuliaLowering.resolve_scopes(ctx2, ex_desugar)
@info "Resolved scopes" ex_scoped formatsrc(ex_scoped, color_by=:var_id)

ctx4, ex_converted = JuliaLowering.convert_closures(ctx3, ex_scoped)
@info "Closure converted" ex_converted formatsrc(ex_converted, color_by=:var_id)

ctx5, ex_compiled = JuliaLowering.linearize_ir(ctx4, ex_converted)
@info "Linear IR" ex_compiled formatsrc(ex_compiled, color_by=:var_id) Text(sprint(JuliaLowering.print_ir, ex_compiled))

ex_expr = JuliaLowering.to_lowered_expr(in_mod, ex_compiled)
@info "CodeInfo" ex_expr

eval_result = Base.eval(in_mod, ex_expr)
@info "Eval" eval_result

