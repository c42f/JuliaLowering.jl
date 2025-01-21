@testset "Miscellanous" begin

test_mod = Module()

# Blocks
@test JuliaLowering.include_string(test_mod, """
begin
end
""") == nothing

# Placeholders
@test JuliaLowering.include_string(test_mod, """_ = 10""") == 10

# GC.@preserve
@test JuliaLowering.include_string(test_mod, """
let x = [1,2]
    GC.@preserve x begin
        x
    end
end        
""") == [1,2]

# ccall
@test ccall(:strlen, Csize_t, (Cstring,), "asdfg") == 5

end
