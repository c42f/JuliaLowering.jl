########################################
# Simple interpolation
quote
    $x + 1
end
#---------------------
1   TestMod.x
2   (call core.tuple %₁)
3   (call JuliaLowering.interpolate_ast SyntaxTree (inert (block (call-i ($ x) + 1))) %₂)
4   (return %₃)

########################################
# Trivial interpolation
:($x)
#---------------------
1   TestMod.x
2   (call core.tuple %₁)
3   (call JuliaLowering.interpolate_ast SyntaxTree (inert ($ x)) %₂)
4   (return %₃)

########################################
# Double escape
quote
    quote
        $$x + 1
    end
end
#---------------------
1   TestMod.x
2   (call core.tuple %₁)
3   (call JuliaLowering.interpolate_ast SyntaxTree (inert (block (quote (block (call-i ($ ($ x)) + 1))))) %₂)
4   (return %₃)

########################################
# Error: Double escape
quote
    $$x + 1
end
#---------------------
LoweringError:
quote
    $$x + 1
#    └┘ ── `$` expression outside string or quote block
end

########################################
# Quoted property access with identifier
Core.:(foo)
#---------------------
1   TestMod.Core
2   (call top.getproperty %₁ :foo)
3   (return %₂)

########################################
# Quoted property access with operator
Core.:(!==)
#---------------------
1   TestMod.Core
2   (call top.getproperty %₁ :!==)
3   (return %₂)

########################################
# Quoted property access on variable
let
    x = (a=1, b=2)
    x.:(a)
end
#---------------------
1   (call core.tuple :a :b)
2   (call core.apply_type core.NamedTuple %₁)
3   (call core.tuple 1 2)
4   (= slot₁/x (call %₂ %₃))
5   slot₁/x
6   (call top.getproperty %₅ :a)
7   (return %₆)
