using JuliaLowering: @islocal
using Base: @locals

#*******************************************************************************
########################################
# let syntax with decl in binding list
let x::T = rhs
    local T = 1
    T # <- This is a different `T` from the T in `x::T`
end
#---------------------
1   TestMod.rhs
2   TestMod.T
3   (newvar slot₁/T)
4   (= slot₃/tmp %₁)
5   slot₃/tmp
6   (call core.isa %₅ %₂)
7   (gotoifnot %₆ label₉)
8   (goto label₁₂)
9   slot₃/tmp
10  (call top.convert %₂ %₉)
11  (= slot₃/tmp (call core.typeassert %₁₀ %₂))
12  slot₃/tmp
13  (= slot₂/x %₁₂)
14  (= slot₁/T 1)
15  slot₁/T
16  (return %₁₅)

########################################
# let syntax with tuple on lhs
let (x,y) = rhs
end
#---------------------
1   TestMod.rhs
2   (call top.indexed_iterate %₁ 1)
3   (= slot₂/x (call core.getfield %₂ 1))
4   (= slot₁/iterstate (call core.getfield %₂ 2))
5   slot₁/iterstate
6   (call top.indexed_iterate %₁ 2 %₅)
7   (= slot₃/y (call core.getfield %₆ 1))
8   (return core.nothing)

########################################
# let syntax with named tuple on lhs creates locals for the unpacked vars
let (; x,y) = rhs
end
#---------------------
1   TestMod.rhs
2   (= slot₁/x (call top.getproperty %₁ :x))
3   (= slot₂/y (call top.getproperty %₁ :y))
4   (return core.nothing)

########################################
# Let syntax with the same name creates nested bindings
let x = f(x), x = g(x)
end
#---------------------
1   TestMod.f
2   TestMod.x
3   (call %₁ %₂)
4   (= slot₁/x %₃)
5   TestMod.g
6   slot₁/x
7   (call %₅ %₆)
8   (= slot₂/x %₇)
9   (return core.nothing)

########################################
# let syntax with a function definition in the binding list creates a closure
let f() = body
end
#---------------------
1   (call core.svec)
2   (call core.svec)
3   (call JuliaLowering.eval_closure_type TestMod :#f##0 %₁ %₂)
4   TestMod.#f##0
5   (new %₄)
6   (= slot₁/f %₅)
7   TestMod.#f##0
8   (call core.svec %₇)
9   (call core.svec)
10  SourceLocation::1:5
11  (call core.svec %₈ %₉ %₁₀)
12  --- method core.nothing %₁₁
    slots: [slot₁/#self#(!read)]
    1   TestMod.body
    2   (return %₁)
13  (return core.nothing)

########################################
# Error: Invalid `let` var with K"::"
let f[]::T = rhs
end
#---------------------
LoweringError:
let f[]::T = rhs
#   └─┘ ── Invalid assignment location in let syntax
end

########################################
# Error: Invalid `let` var
let f[] = rhs
end
#---------------------
LoweringError:
let f[] = rhs
#   └─┘ ── Invalid assignment location in let syntax
end

########################################
# Error: Invalid function def in `let`
let (obj::Callable)() = rhs
end
#---------------------
LoweringError:
let (obj::Callable)() = rhs
#   └───────────────┘ ── Function signature does not define a local function name
end

########################################
# @islocal with locals and undefined vars
let x = 1
    @islocal(a), @islocal(x)
end
#---------------------
1   1
2   (= slot₁/x %₁)
3   (call core.tuple false true)
4   (return %₃)

########################################
# @islocal with function arguments
begin
    local y = 2
    function f(x)
        @islocal(a), @islocal(x), @islocal(y)
    end
end
#---------------------
1   (= slot₁/y (call core.Box))
2   2
3   slot₁/y
4   (call core.setfield! %₃ :contents %₂)
5   (method TestMod.f)
6   TestMod.f
7   (call core.Typeof %₆)
8   (call core.svec %₇ core.Any)
9   (call core.svec)
10  SourceLocation::3:14
11  (call core.svec %₈ %₉ %₁₀)
12  --- method core.nothing %₁₁
    slots: [slot₁/#self#(!read) slot₂/x(!read)]
    1   (call core.tuple false true true)
    2   (return %₁)
13  TestMod.f
14  (return %₁₃)

########################################
# @islocal with global
begin
    global x
    @islocal(x)
end
#---------------------
1   (global TestMod.x)
2   (return false)

########################################
# @locals with local and global
begin
    global x
    local y
    @locals
end
#---------------------
1   (newvar slot₁/y)
2   (global TestMod.x)
3   (call core.apply_type top.Dict core.Symbol core.Any)
4   (call %₃)
5   (isdefined slot₁/y)
6   (gotoifnot %₅ label₉)
7   slot₁/y
8   (call top.setindex! %₄ %₇ :y)
9   (return %₄)

########################################
# @locals with function args (TODO: static parameters)
function f(z)
    @locals
end
#---------------------
1   (method TestMod.f)
2   TestMod.f
3   (call core.Typeof %₂)
4   (call core.svec %₃ core.Any)
5   (call core.svec)
6   SourceLocation::1:10
7   (call core.svec %₄ %₅ %₆)
8   --- method core.nothing %₇
    slots: [slot₁/#self#(!read) slot₂/z]
    1   (call core.apply_type top.Dict core.Symbol core.Any)
    2   (call %₁)
    3   (gotoifnot true label₅)
    4   (call top.setindex! %₂ slot₂/z :z)
    5   (return %₂)
9   TestMod.f
10  (return %₉)

########################################
# Error: Duplicate function argument names
function f(x, x)
end
#---------------------
LoweringError:
function f(x, x)
#             ╙ ── function argument name not unique
end

########################################
# Error: Duplicate function argument with destructured arg
function f(x, (x,))
end
#---------------------
LoweringError:
function f(x, (x,))
#              ╙ ── function argument name not unique
end

########################################
# Error: Static parameter name not unique
function f(::T) where T where T
end
#---------------------
LoweringError:
function f(::T) where T where T
#                     ╙ ── function static parameter name not unique
end

########################################
# Error: static parameter colliding with argument names
function f(x::x) where x
end
#---------------------
LoweringError:
function f(x::x) where x
#                      ╙ ── static parameter name not distinct from function argument
end

########################################
# Error: duplicate destructure args
function f((x,), (x,))
end
#---------------------
LoweringError:
function f((x,), (x,))
#                 ╙ ── function argument name not unique
end

########################################
# Error: Conflicting local and global decls
let
    local x
    global x
end
#---------------------
LoweringError:
let
    local x
    global x
#   └──────┘ ── Variable `x` declared both local and global
end

########################################
# Error: Conflicting argument and local
function f(x)
    local x
end
#---------------------
LoweringError:
function f(x)
    local x
#   └─────┘ ── local variable name `x` conflicts with an argument
end

########################################
# Error: Conflicting argument and global
function f(x)
    global x
end
#---------------------
LoweringError:
function f(x)
    global x
#   └──────┘ ── global variable name `x` conflicts with an argument
end

########################################
# Error: Conflicting destructured argument and global
# TODO: The error could probably be a bit better here
function f((x,))
    global x
end
#---------------------
LoweringError:
function f((x,))
    global x
#   └──────┘ ── Variable `x` declared both local and global
end

########################################
# Error: Conflicting static parameter and local
function f(::T) where T
    local T
end
#---------------------
LoweringError:
function f(::T) where T
    local T
#   └─────┘ ── local variable name `T` conflicts with a static parameter
end

########################################
# Error: Conflicting static parameter and global
function f(::T) where T
    global T
end
#---------------------
LoweringError:
function f(::T) where T
    global T
#   └──────┘ ── global variable name `T` conflicts with a static parameter
end

########################################
# Error: Conflicting static parameter and local in nested scope
function f(::T) where T
    let
        local T
    end
end
#---------------------
LoweringError:
function f(::T) where T
    let
        local T
#       └─────┘ ── local variable name `T` conflicts with a static parameter
    end
end

########################################
# Error: Conflicting static parameter and global in nested scope
function f(::T) where T
    let
        global T
    end
end
#---------------------
LoweringError:
function f(::T) where T
    let
        global T
#       └──────┘ ── global variable name `T` conflicts with a static parameter
    end
end

########################################
# Error: Conflicting static parameter and implicit local
function f(::T) where T
    let
        T = rhs
    end
end
#---------------------
LoweringError:
function f(::T) where T
    let
        T = rhs
#       ╙ ── local variable name `T` conflicts with a static parameter
    end
end

########################################
# Error: Attempt to add methods to a function argument
function f(g)
    function g()
    end
end
#---------------------
LoweringError:
function f(g)
    function g()
#            ╙ ── Cannot add method to a function argument
    end
end

########################################
# Error: Global method definition inside function scope
function f()
    global global_method
    function global_method()
    end
end
#---------------------
LoweringError:
function f()
    global global_method
    function global_method()
#            └───────────┘ ── Global method definition needs to be placed at the top level, or use `eval()`
    end
end

########################################
# @isdefined with defined variables
let x = 1
    @isdefined x
    @isdefined y
end
#---------------------
1   1
2   (= slot₁/x %₁)
3   (isdefined TestMod.y)
4   (return %₃)

