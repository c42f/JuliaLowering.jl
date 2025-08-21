########################################
# Basic import
import A: b
#---------------------
1   (call top._eval_import true TestMod :($(QuoteNode(:($(Expr(:., :A)))))) :($(QuoteNode(:($(Expr(:., :b)))))))
2   latestworld
3   (return core.nothing)

########################################
# Import with paths and `as`
import A.B.C: b, c.d as e
#---------------------
1   (call top._eval_import true TestMod :($(QuoteNode(:($(Expr(:., :A, :B, :C)))))) :($(QuoteNode(:($(Expr(:., :b)))))) :($(QuoteNode(:(c.d as e)))))
2   latestworld
3   (return core.nothing)

########################################
# Using
using A
#---------------------
1   (call top._eval_using TestMod :($(QuoteNode(:($(Expr(:., :A)))))))
2   latestworld
3   (return core.nothing)

########################################
# Using with paths and `as`
using A.B.C: b, c.d as e
#---------------------
1   (call top._eval_import false TestMod :($(QuoteNode(:($(Expr(:., :A, :B, :C)))))) :($(QuoteNode(:($(Expr(:., :b)))))) :($(QuoteNode(:(c.d as e)))))
2   latestworld
3   (return core.nothing)

########################################
# Error: Import not at top level
function f()
    import A: b
end
#---------------------
LoweringError:
function f()
    import A: b
#   └─────────┘ ── this syntax is only allowed in top level code
end

########################################
# Export
export a, b, c
#---------------------
1   (call JuliaLowering.eval_public TestMod true ["a", "b", "c"])
2   (return %₁)

########################################
# Public
public a, b, c
#---------------------
1   (call JuliaLowering.eval_public TestMod false ["a", "b", "c"])
2   (return %₁)

