@testset "Miscellanous" begin

test_mod = Module()

# Blocks
@test JuliaLowering.include_string(test_mod, """
begin
end
""") == nothing

# Placeholders
@test JuliaLowering.include_string(test_mod, """_ = 10""") == 10

end