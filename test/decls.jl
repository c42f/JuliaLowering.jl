@testset "Declarations" begin

test_mod = Module()

@test JuliaLowering.include_string(test_mod, """
begin
    local x::Int = 1.0
    x
end
""") === 1

# In value position, yeild the right hand side, not `x`
@test JuliaLowering.include_string(test_mod, """
local x::Int = 1.0
""") === 1.0

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

# Const and tuple assignments
@test JuliaLowering.include_string(test_mod, "(a0, a1, a2) = [1,2,3]") == [1,2,3]

@test JuliaLowering.include_string(test_mod, "const abc::Int = 9") === 9

# redeclaration of the same value used to be allowed
@test_throws ErrorException JuliaLowering.include_string(test_mod, "abc = 9")
@test_throws ErrorException JuliaLowering.include_string(test_mod, "abc = 10")
# redeclaration with const should be OK
@test JuliaLowering.include_string(test_mod, "const abc::Int = 0") === 0

# Unsupported for now
@test_throws LoweringError JuliaLowering.include_string(test_mod, "const a,b,c = 1,2,3")

end
