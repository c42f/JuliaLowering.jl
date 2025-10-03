@testset "Declarations" begin

test_mod = Module()

@test JuliaLowering.include_string(test_mod, """
begin
    local x::Int = 1.0
    x
end
""") === 1

# In value position, yield the right hand side, not `x`
@test JuliaLowering.include_string(test_mod, """
begin
    local x::Int = 1.0
end
""") === 1.0

# Global decl in value position without assignment returns nothing
@test JuliaLowering.include_string(test_mod, "global x_no_assign") === nothing

# Unadorned declarations
@test JuliaLowering.include_string(test_mod, """
let
    a = 0.0
    x::Int = a
    x
end
""") === 0

@test JuliaLowering.include_string(test_mod, """
let
    local x::Int = 1
    x1 = x
    x = 20.0
    x2 = x
    (x1,x2)
end
""") === (1, 20)

# Global const mixes
@test JuliaLowering.include_string(test_mod, "global x_g = 1") === 1
@test Base.isdefinedglobal(test_mod, :x_g)
@test !Base.isconst(test_mod, :x_g)
@test test_mod.x_g === 1

@test JuliaLowering.include_string(test_mod, "const x_c = 1") === 1
@test Base.isdefinedglobal(test_mod, :x_c)
@test Base.isconst(test_mod, :x_c)
@test test_mod.x_c === 1

@test JuliaLowering.include_string(test_mod, "global const x_gc = 1") === 1
@test Base.isdefinedglobal(test_mod, :x_gc)
@test Base.isconst(test_mod, :x_gc)
@test test_mod.x_gc === 1

@test JuliaLowering.include_string(test_mod, "const global x_cg = 1") === 1
@test Base.isdefinedglobal(test_mod, :x_cg)
@test Base.isconst(test_mod, :x_cg)
@test test_mod.x_cg === 1
# Possibly worth testing excessive global/const keywords or invalid combinations
# (local + global/const) once we decide whether that's a parse error or a
# lowering error

# Global decls with types
@test JuliaLowering.include_string(test_mod, """
global a_typed_global::Int = 10.0
""") === 10.0
@test Core.get_binding_type(test_mod, :a_typed_global) === Int
@test test_mod.a_typed_global === 10

# Also allowed in nontrivial scopes in a top level thunk
@test JuliaLowering.include_string(test_mod, """
let
    global a_typed_global_2::Int = 10.0
end
""") === 10.0
@test Core.get_binding_type(test_mod, :a_typed_global_2) === Int
@test test_mod.a_typed_global_2 === 10

@test JuliaLowering.include_string(test_mod, "const x_c_T::Int = 9") === 9
@test Base.isdefinedglobal(test_mod, :x_c_T)
@test Base.isconst(test_mod, :x_c_T)

@testset "typed const redeclaration" begin
    # redeclaration of the same value used to be allowed
    @test_throws ErrorException JuliaLowering.include_string(test_mod, "x_c_T = 9")
    @test_throws ErrorException JuliaLowering.include_string(test_mod, "x_c_T = 10")
    # redeclaration with const should be OK
    @test JuliaLowering.include_string(test_mod, "const x_c_T::Int = 0") === 0
end

# Tuple/destructuring assignments
@test JuliaLowering.include_string(test_mod, "(a0, a1, a2) = [1,2,3]") == [1,2,3]


# Unsupported for now
@test_throws LoweringError JuliaLowering.include_string(test_mod, "const a,b,c = 1,2,3")

@testset "global function in let" begin
    # Basic case: short form function syntax
    @test JuliaLowering.include_string(test_mod, """
    let x = 42
        global getx1() = x
    end
    """) == test_mod.getx1
    @test test_mod.getx1() === 42

    # Long form function syntax
    @test JuliaLowering.include_string(test_mod, """
    let y = 100
        global function gety1()
            y
        end
    end
    """) == test_mod.gety1
    @test test_mod.gety1() === 100

    # Multiple global functions in same let
    @test JuliaLowering.include_string(test_mod, """
    let val = 7
        global getval1() = val
        global setval1(v) = (val = v)
    end
    """) == test_mod.setval1
    @test test_mod.getval1() === 7
    test_mod.setval1(20)
    @test test_mod.getval1() === 20

    # Type-qualified function
    JuliaLowering.include_string(test_mod, """
    struct TestCallable1 end
    let x = 99
        global (::TestCallable1)() = x
    end
    """)
    @test test_mod.TestCallable1()() === 99

    # Function with where clause
    @test JuliaLowering.include_string(test_mod, """
    let data = [1,2,3]
        global getdata1(::Type{T}) where T = T.(data)
    end
    """) == test_mod.getdata1
    @test test_mod.getdata1(Float64) == [1.0, 2.0, 3.0]
end

@testset "local function declaration" begin
    @test JuliaLowering.include_string(test_mod, """
    let
        local f() = 42
        f()
    end
    """) === 42

    # Local function should not leak out
    @test !Base.isdefinedglobal(test_mod, :f)
end

# Qualified names should work (no declaration added)
@testset "qualified function names" begin
    JuliaLowering.include_string(test_mod, """
    module TestMod1
        f() = 1
    end
    """)

    @test JuliaLowering.include_string(test_mod, """
    global TestMod1.f(x::Int) = x + 1
    """) === nothing
    @test test_mod.TestMod1.f(5) === 6

    @test JuliaLowering.include_string(test_mod, """
    let
        global TestMod1.f(x::Float64) = x + 1
    end
    """) === nothing
    @test test_mod.TestMod1.f(5.0) === 6.0
end

# Error cases
@test_throws LoweringError JuliaLowering.include_string(test_mod, """
let
    local func(x) = x
    global func(x) = x
end
""")

end
