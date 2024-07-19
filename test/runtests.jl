using Test

include("utils.jl")

@testset "JuliaLowering.jl" begin

include("syntax_graph.jl")

# Basic end-to-end / smoke tests

test_mod = Module()

#-------------------------------------------------------------------------------
# Scopes
@test JuliaLowering.include_string(test_mod,
"""
let
    y = 0
    x = 1
    let x = x + 1
        y = x
    end
    (x, y)
end
""") == (1, 2)

JuliaLowering.include_string(test_mod, """
    x = 101
    y = 202
""")
@test test_mod.x == 101
@test test_mod.y == 202
@test JuliaLowering.include_string(test_mod, "x + y") == 303

# wrap expression in scope block of `scope_type`
function wrapscope(ex, scope_type)
    g = JuliaLowering.ensure_attributes(ex._graph, scope_type=Symbol)
    ex = JuliaLowering.reparent(g, ex)
    makenode(ex, ex, K"scope_block", ex; scope_type=scope_type)
end

assign_z_2 = parsestmt(SyntaxTree, "begin z = 2 end", filename="foo.jl")
JuliaLowering.eval(test_mod, :(z=1))
@test test_mod.z == 1
# neutral (eg, for loops) and hard (eg, let) scopes create a new binding for z
JuliaLowering.eval(test_mod, wrapscope(assign_z_2, :neutral))
@test test_mod.z == 1
JuliaLowering.eval(test_mod, wrapscope(assign_z_2, :hard))
@test test_mod.z == 1
# but wrapping neutral scope in soft scope uses the existing binding in test_mod
JuliaLowering.eval(test_mod, wrapscope(wrapscope(assign_z_2, :neutral), :soft))
@test test_mod.z == 2

#-------------------------------------------------------------------------------
# Placeholders
@test JuliaLowering.include_string(test_mod, """_ = 10""") == 10

assign_underscore = parsestmt(SyntaxTree, "_ + 1", filename="foo.jl")
exc = try
    JuliaLowering.eval(test_mod, assign_underscore)
catch exc
    exc
end
@test exc.msg == "all-underscore identifiers are write-only and their values cannot be used in expressions"
@test JuliaLowering.is_ancestor(exc.ex, assign_underscore[1])

#-------------------------------------------------------------------------------
# Function calls
# Splatting
@test JuliaLowering.include_string(test_mod, """
let
    x = 1
    y = 2
    zs = (3,4)
    w = 5
    (tuple(zs...),
     tuple(zs..., w),
     tuple(y, zs...),
     tuple(x, y, zs..., w))
end
""") == ((3,4),
         (3,4,5),
         (2,3,4),
         (1,2,3,4,5))

#-------------------------------------------------------------------------------
# Functions
@test JuliaLowering.include_string(test_mod, """
begin
    function f(x)
        y = x + 1
        "hi", x, y
    end

    f(1)
end
""") == ("hi", 1, 2)


#-------------------------------------------------------------------------------
# module
A = JuliaLowering.include_string(test_mod, """
module A
    function g()
        return "hi"
    end
end
""", "module_test")
@test A isa Module
@test A.g() == "hi"
@test A.include isa Function
@test A.Base === Base
@test A.eval(:(x = -1)) == -1 && A.x == -1

B = JuliaLowering.include_string(test_mod, """
baremodule B
end
""", "baremodule_test")
@test B.Core === Core
@test !isdefined(B, :include)
@test !isdefined(B, :Base)

#-------------------------------------------------------------------------------
# using / import
JuliaLowering.include_string(test_mod, """
    using JuliaSyntax
    using JuliaLowering: SyntaxTree
    using JuliaLowering: SyntaxTree as st
    import JuliaLowering: SyntaxTree as st1, SyntaxTree as st2
""")
@test test_mod.SyntaxTree === JuliaLowering.SyntaxTree
@test test_mod.st === JuliaLowering.SyntaxTree
@test test_mod.st1 === JuliaLowering.SyntaxTree
@test test_mod.st2 === JuliaLowering.SyntaxTree
@test test_mod.parsestmt === JuliaSyntax.parsestmt

C = JuliaLowering.include_string(test_mod, """
module C
    module D
        function f()
            "hi"
        end
    end
    module E
        using ...C.D: f
    end
end
""")
@test C.D.f === C.E.f

#-------------------------------------------------------------------------------
# Macro expansion

JuliaLowering.include_string(test_mod, """
module M
    using JuliaLowering: JuliaLowering, @ast, @chk, adopt_scope
    using JuliaSyntax

    # Introspection
    macro __MODULE__()
        __context__.scope_layer.mod
    end

    macro __FILE__()
        JuliaLowering.filename(__context__.macroname)
    end

    macro __LINE__()
        JuliaLowering.source_location(__context__.macroname)[1]
    end

    someglobal = "global in module M"

    # Macro with local variables
    macro foo(ex)
        :(begin
            x = "`x` from @foo"
            (x, someglobal, \$ex)
        end)
    end

    # Set `a_global` in M
    macro set_a_global(val)
        :(begin
            global a_global = \$val
        end)
    end

    macro set_other_global(ex, val)
        :(begin
            global \$ex = \$val
        end)
    end

    macro set_global_in_parent(ex)
        e1 = adopt_scope(:(sym_introduced_from_M), __context__)
        quote
            \$e1 = \$ex
            nothing
        end
    end

    macro inner()
        :(2)
    end

    macro outer()
        :((1, @inner))
    end

    # # Recursive macro call
    # # TODO: Need branching!
    # macro recursive(N)
    #     Nval = N.value #::Int
    #     if Nval < 1
    #         return N
    #     end
    #     quote
    #         x = \$N
    #         (@recursive \$(Nval-1), x)
    #     end
    # end
end
""")

@test JuliaLowering.include_string(test_mod, """
let 
    x = "`x` from outer scope"
    M.@foo x
end
""") == ("`x` from @foo", "global in module M", "`x` from outer scope")
@test !isdefined(test_mod.M, :x)

@test JuliaLowering.include_string(test_mod, """
#line1
(M.@__MODULE__(), M.@__FILE__(), M.@__LINE__())
""", "foo.jl") == (test_mod, "foo.jl", 2)

@test !isdefined(test_mod.M, :a_global)
@test JuliaLowering.include_string(test_mod, """
begin 
    M.@set_a_global 42
    M.a_global
end
""") == 42

JuliaLowering.include_string(test_mod, """
M.@set_global_in_parent "bent hygiene!"
""")
@test test_mod.sym_introduced_from_M == "bent hygiene!"

JuliaLowering.include_string(test_mod, "M.@set_other_global global_in_test_mod 100")
@test !isdefined(test_mod.M, :global_in_test_mod)
@test test_mod.global_in_test_mod == 100

Base.eval(test_mod.M, :(
# Recursive macro call
function var"@recursive"(mctx, N)
    @chk kind(N) == K"Integer"
    Nval = N.value::Int
    if Nval < 1
        return N
    end
    @ast mctx (@HERE) [K"block"
        [K"="(@HERE)
            "x"::K"Identifier"(@HERE)
            N
        ]
        [K"tuple"(@HERE)
            "x"::K"Identifier"(@HERE)
            [K"macrocall"(@HERE)
                "@recursive"::K"Identifier"
                (Nval-1)::K"Integer"
            ]
        ]
    ]
end
))

@test JuliaLowering.include_string(test_mod, """
M.@recursive 3
""") == (3, (2, (1, 0)))

@test let
    ex = parsestmt(SyntaxTree, "M.@outer()", filename="foo.jl")
    expanded = JuliaLowering.macroexpand(test_mod, ex)
    sourcetext.(flattened_provenance(expanded[2]))
end == [
    "M.@outer()"
    "@inner"
    "2"
]


@test_throws JuliaLowering.LoweringError JuliaLowering.include_string(test_mod, """
macro mmm(a; b=2)
end
""")

@test_throws JuliaLowering.LoweringError JuliaLowering.include_string(test_mod, """
macro A.b(ex)
end
""")

include("branching.jl")
include("loops.jl")

end
