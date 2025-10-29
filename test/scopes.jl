@testset "Scopes" begin

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

@test JuliaLowering.include_string(test_mod, """
begin
    local x = 1
    local x = 2
    let (x,y) = (:x,:y)
        (y,x)
    end
end
""") === (:y,:x)

# Types on left hand side of type decls refer to the outer scope
# (In the flisp implementation they refer to the inner scope, but this seems
# like a bug.)
@test JuliaLowering.include_string(test_mod, """
let x::Int = 10.0
    local Int = Float64
    x
end
""") === 10

# Closures in let syntax can only capture values from the outside
# (In the flisp implementation it captures from inner scope, but this is
# inconsistent with let assignment where the rhs refers to the outer scope and
# thus seems like a bug.)
@test JuliaLowering.include_string(test_mod, """
begin
    local y = :outer_y
    let f() = y
        local y = :inner_y
        f()
    end
end
""") === :outer_y

# wrap expression in scope block of `scope_type`
function wrapscope(ex, scope_type)
    g = JuliaLowering.ensure_attributes(ex._graph, scope_type=Symbol)
    ex = JuliaLowering.reparent(g, ex)
    makenode(ex, ex, K"scope_block", ex; scope_type=scope_type)
end

assign_z_2 = parsestmt(SyntaxTree, "begin z = 2 end", filename="foo.jl")
Base.eval(test_mod, :(z=1))
@test test_mod.z == 1
# neutral (eg, for loops) and hard (eg, let) scopes create a new binding for z
JuliaLowering.eval(test_mod, wrapscope(assign_z_2, :neutral))
@test test_mod.z == 1
JuliaLowering.eval(test_mod, wrapscope(assign_z_2, :hard))
@test test_mod.z == 1
# but wrapping neutral scope in soft scope uses the existing binding in test_mod
JuliaLowering.eval(test_mod, wrapscope(wrapscope(assign_z_2, :neutral), :soft))
@test test_mod.z == 2

@testset "top-level function defs aren't local to soft scopes" begin
    def = parsestmt(SyntaxTree, "function f_softscope_test(); 1; end", filename="foo.jl")
    JuliaLowering.eval(test_mod, wrapscope(def, :hard))
    @test !isdefined(test_mod, :f_softscope_test)
    JuliaLowering.eval(test_mod, wrapscope(def, :neutral))
    @test !isdefined(test_mod, :f_softscope_test)
    JuliaLowering.eval(test_mod, wrapscope(def, :soft))
    @test isdefined(test_mod, :f_softscope_test)

    JuliaLowering.include_string(test_mod, """
    for i in 1
        fdecl_in_loop() = 1
    end
    """)
    @test !isdefined(test_mod, :fdecl_in_loop)
end

@testset "constdecls OK in soft scopes" begin
    def = parsestmt(SyntaxTree, "const c_softscope_test = 1", filename="foo.jl")
    @test_throws LoweringError JuliaLowering.eval(test_mod, wrapscope(def, :hard))
    @test_throws LoweringError JuliaLowering.eval(test_mod, wrapscope(def, :neutral))
    JuliaLowering.eval(test_mod, wrapscope(def, :soft))
    @test isdefined(test_mod, :c_softscope_test)
end

@eval test_mod module macro_mod
    macro m(x); x; end
    macro mesc(x); esc(x); end
end

@testset "top-level function defs aren't local in macro expansions" begin
    JuliaLowering.include_string(test_mod, "macro_mod.@m function f_nonlocal_1(); 1; end")
    @test isdefined(test_mod.macro_mod, :f_nonlocal_1)
    JuliaLowering.include_string(test_mod, "macro_mod.@mesc function f_nonlocal_2(); 1; end")
    @test isdefined(test_mod, :f_nonlocal_2)
    # Note: for the particular case of an unescaped top-level const declaration,
    # flisp makes it macro-local (i.e. mangles the name), but this isn't the
    # case for other globals (top-level functions decls, global decls, types) so
    # it might be a bug.
    JuliaLowering.include_string(test_mod, "macro_mod.@m const c_nonlocal_1 = 1")
    @test isdefined(test_mod.macro_mod, :c_nonlocal_1)
    # Our behaviour is the same when the const is escaped
    JuliaLowering.include_string(test_mod, "macro_mod.@mesc const c_nonlocal_2 = 1")
    @test isdefined(test_mod, :c_nonlocal_2)
end

end
