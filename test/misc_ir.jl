########################################
# Getproperty syntax
x.a
#---------------------
1   TestMod.x
2   (call top.getproperty %₁ :a)
3   (return %₂)

########################################
# Getproperty syntax with a string on right hand side
x."b"
#---------------------
1   TestMod.x
2   (call top.getproperty %₁ "b")
3   (return %₂)

########################################
# Standalone dot syntax
.*
#---------------------
1   TestMod.*
2   (call top.BroadcastFunction %₁)
3   (return %₂)

########################################
# Error: Wrong number of children in `.`
@ast_ [K"." "x"::K"Identifier" "a"::K"Identifier" 3::K"Integer"]
#---------------------
LoweringError:
#= line 1 =# - `.` form requires either one or two children

########################################
# Error: Placeholder value used
_ + 1
#---------------------
LoweringError:
_ + 1
╙ ── all-underscore identifiers are write-only and their values cannot be used in expressions

########################################
# Named tuple
(a=1, b=2)
#---------------------
1   (call core.tuple :a :b)
2   (call core.apply_type core.NamedTuple %₁)
3   (call core.tuple 1 2)
4   (call %₂ %₃)
5   (return %₄)

########################################
# Named tuple with parameters
(; a=1, b=2)
#---------------------
1   (call core.tuple :a :b)
2   (call core.apply_type core.NamedTuple %₁)
3   (call core.tuple 1 2)
4   (call %₂ %₃)
5   (return %₄)

########################################
# Empty named tuple
(;)
#---------------------
1   (call core.NamedTuple)
2   (return %₁)

########################################
# Named tuple with implicit field names
(;x, a.b.c, y._)
#---------------------
1   (call core.tuple :x :c :_)
2   (call core.apply_type core.NamedTuple %₁)
3   TestMod.x
4   TestMod.a
5   (call top.getproperty %₄ :b)
6   (call top.getproperty %₅ :c)
7   TestMod.y
8   (call top.getproperty %₇ :_)
9   (call core.tuple %₃ %₆ %₈)
10  (call %₂ %₉)
11  (return %₁₀)

########################################
# Named tuple with splats
(; a=1, b=2, bs..., c=3, ds...)
#---------------------
1   (call core.tuple :a :b)
2   (call core.apply_type core.NamedTuple %₁)
3   (call core.tuple 1 2)
4   (call %₂ %₃)
5   TestMod.bs
6   (call top.merge %₄ %₅)
7   (call core.tuple :c)
8   (call core.apply_type core.NamedTuple %₇)
9   (call core.tuple 3)
10  (call %₈ %₉)
11  (call top.merge %₆ %₁₀)
12  TestMod.ds
13  (call top.merge %₁₁ %₁₂)
14  (return %₁₃)

########################################
# Named tuple with only splats
(; as..., bs...)
#---------------------
1   (call core.NamedTuple)
2   TestMod.as
3   (call top.merge %₁ %₂)
4   TestMod.bs
5   (call top.merge %₃ %₄)
6   (return %₅)

########################################
# Named tuple with dynamic names
(; a=1, b=2, c=>d)
#---------------------
1   (call core.tuple :a :b)
2   (call core.apply_type core.NamedTuple %₁)
3   (call core.tuple 1 2)
4   (call %₂ %₃)
5   TestMod.c
6   (call core.tuple %₅)
7   (call core.apply_type core.NamedTuple %₆)
8   TestMod.d
9   (call core.tuple %₈)
10  (call %₇ %₉)
11  (call top.merge %₄ %₁₀)
12  (return %₁₁)

########################################
# Error: Named tuple with repeated fields
(; a=1, bs..., c=3, a=2)
#---------------------
LoweringError:
(; a=1, bs..., c=3, a=2)
#                   ╙ ── Repeated named tuple field name

########################################
# Error: Named tuple frankentuple
(a=1; b=2, c=3)
#---------------------
LoweringError:
(a=1; b=2, c=3)
#   └────────┘ ── unexpected semicolon in tuple - use `,` to separate tuple elements

########################################
# Error: Named tuple field dots in rhs
(; a=xs...)
#---------------------
LoweringError:
(; a=xs...)
#    └───┘ ── `...` cannot be used in a value for a named tuple field

########################################
# Error: Named tuple field invalid lhs
(; a[]=1)
#---------------------
LoweringError:
(; a[]=1)
#  └─┘ ── invalid named tuple field name

########################################
# Error: Named tuple element with weird dot syntax
(; a."b")
#---------------------
LoweringError:
(; a."b")
#  └───┘ ── invalid named tuple element

########################################
# Error: Named tuple element without valid name
(; a=1, f())
#---------------------
LoweringError:
(; a=1, f())
#       └─┘ ── Invalid named tuple element

########################################
# Error: Modules not allowed in local scope
let
    module C
    end
end
#---------------------
LoweringError:
let
#   ┌───────
    module C
    end
#─────┘ ── module is only allowed in global scope
end

########################################
# Error: Modules not allowed in local scope
function f()
    module C
    end
end
#---------------------
LoweringError:
function f()
#   ┌───────
    module C
    end
#─────┘ ── module is only allowed in global scope
end

########################################
# Basic type assert
x::T
#---------------------
1   TestMod.x
2   TestMod.T
3   (call core.typeassert %₁ %₂)
4   (return %₃)

########################################
# Error: Invalid :: syntax outside function arg list
::T
#---------------------
LoweringError:
::T
└─┘ ── `::` must be written `value::type` outside function argument lists

########################################
# Error: braces vector syntax
{x, y}
#---------------------
LoweringError:
{x, y}
└────┘ ── { } syntax is reserved for future use

########################################
# Error: braces matrix syntax
{x y; y z}
#---------------------
LoweringError:
{x y; y z}
└────────┘ ── { } syntax is reserved for future use

########################################
# Error: Test AST which has no source form and thus must have been constructed
# programmatically (eg, a malformed if)
@ast_ [K"if"]
#---------------------
LoweringError:
#= line 1 =# - expected `numchildren(ex) >= 2`

########################################
# Error: @atomic in wrong position
let
    @atomic x
end
#---------------------
LoweringError:
let
    @atomic x
#   └───────┘ ── unimplemented or unsupported atomic declaration
end

########################################
# GC.@preserve support
GC.@preserve a b begin
    f(a,b)
end
#---------------------
1   TestMod.a
2   TestMod.b
3   (= slot₂/s (gc_preserve_begin %₁ %₂))
4   TestMod.f
5   TestMod.a
6   TestMod.b
7   (= slot₁/r (call %₄ %₅ %₆))
8   (gc_preserve_end slot₂/s)
9   slot₁/r
10  (return %₉)

########################################
# Error: GC.@preserve bad args
GC.@preserve a b g() begin
    body
end
#---------------------
MacroExpansionError while expanding (. GC @preserve) in module Main.TestMod:
GC.@preserve a b g() begin
#                └─┘ ── Preserved variable must be a symbol
    body
end

########################################
# Juxtaposition
20x
#---------------------
1   TestMod.*
2   TestMod.x
3   (call %₁ 20 %₂)
4   (return %₃)

########################################
# basic ccall
ccall(:strlen, Csize_t, (Cstring,), "asdfg")
#---------------------
1   TestMod.Cstring
2   (call top.cconvert %₁ "asdfg")
3   (call top.unsafe_convert %₁ %₂)
4   (foreigncall :strlen TestMod.Csize_t (call core.svec TestMod.Cstring) 0 :ccall %₃ %₂)
5   (return %₄)

########################################
# ccall with library name as a global var
ccall((:strlen, libc), Csize_t, (Cstring,), "asdfg")
#---------------------
1   TestMod.Cstring
2   (call top.cconvert %₁ "asdfg")
3   TestMod.libc
4   (call core.tuple :strlen %₃)
5   (call top.unsafe_convert %₁ %₂)
6   (foreigncall %₄ TestMod.Csize_t (call core.svec TestMod.Cstring) 0 :ccall %₅ %₂)
7   (return %₆)

########################################
# ccall with a calling convention
ccall(:foo, stdcall, Csize_t, ())
#---------------------
1   (foreigncall :foo TestMod.Csize_t (call core.svec) 0 :stdcall)
2   (return %₁)

########################################
# ccall with Any args become core.Any and don't need conversion or GC roots
ccall(:foo, stdcall, Csize_t, (Any,), x)
#---------------------
1   core.Any
2   TestMod.x
3   (foreigncall :foo TestMod.Csize_t (call core.svec core.Any) 0 :stdcall %₂)
4   (return %₃)

########################################
# ccall with variable as function name (must eval to a pointer)
ccall(ptr, Csize_t, (Cstring,), "asdfg")
#---------------------
1   TestMod.Cstring
2   (call top.cconvert %₁ "asdfg")
3   TestMod.ptr
4   (call top.unsafe_convert %₁ %₂)
5   (foreigncall %₃ TestMod.Csize_t (call core.svec TestMod.Cstring) 0 :ccall %₄ %₂)
6   (return %₅)

########################################
# ccall with varargs
ccall(:printf, Cint, (Cstring, Cstring...), "%s = %s\n", "2 + 2", "5")
#---------------------
1   TestMod.Cstring
2   TestMod.Cstring
3   (call top.cconvert %₁ "%s = %s\n")
4   (call top.cconvert %₂ "2 + 2")
5   (call top.cconvert %₂ "5")
6   (call top.unsafe_convert %₁ %₃)
7   (call top.unsafe_convert %₂ %₄)
8   (call top.unsafe_convert %₂ %₅)
9   (foreigncall :printf TestMod.Cint (call core.svec TestMod.Cstring TestMod.Cstring TestMod.Cstring) 1 :ccall %₆ %₇ %₈ %₃ %₄ %₅)
10  (return %₉)

########################################
# Error: ccall with too few arguments
ccall(:foo, Csize_t)
#---------------------
LoweringError:
ccall(:foo, Csize_t)
└──────────────────┘ ── too few arguments to ccall

########################################
# Error: ccall with calling conv and too few arguments
ccall(:foo, thiscall, Csize_t)
#---------------------
LoweringError:
ccall(:foo, thiscall, Csize_t)
└────────────────────────────┘ ── too few arguments to ccall with calling convention specified

########################################
# Error: ccall without tuple for argument types
ccall(:foo, Csize_t, Cstring)
#---------------------
LoweringError:
ccall(:foo, Csize_t, Cstring)
#                    └─────┘ ── ccall argument types must be a tuple; try `(T,)`

########################################
# Error: ccall without tuple for argument types
ccall(:foo, (Csize_t,), "arg")
#---------------------
LoweringError:
ccall(:foo, (Csize_t,), "arg")
#           └────────┘ ── ccall argument types must be a tuple; try `(T,)` and check if you specified a correct return type

########################################
# Error: ccall with library name which is a local variable
let libc = "libc"
    ccall((:strlen, libc), Csize_t, (Cstring,), "asdfg")
end
#---------------------
LoweringError:
let libc = "libc"
    ccall((:strlen, libc), Csize_t, (Cstring,), "asdfg")
#         └─────────────┘ ── ccall function name and library expression cannot reference local variables
end

########################################
# Error: ccall with return type which is a local variable
let Csize_t = 1
    ccall(:strlen, Csize_t, (Cstring,), "asdfg")
end
#---------------------
LoweringError:
let Csize_t = 1
    ccall(:strlen, Csize_t, (Cstring,), "asdfg")
#                  └─────┘ ── ccall return type cannot reference local variables
end

########################################
# Error: ccall with argument type which is a local variable
let Cstring = 1
    ccall(:strlen, Csize_t, (Cstring,), "asdfg")
end
#---------------------
LoweringError:
let Cstring = 1
    ccall(:strlen, Csize_t, (Cstring,), "asdfg")
#                            └─────┘ ── ccall argument types cannot reference local variables
end

########################################
# Error: ccall with too few arguments
ccall(:strlen, Csize_t, (Cstring,))
#---------------------
LoweringError:
ccall(:strlen, Csize_t, (Cstring,))
└─────────────────────────────────┘ ── Too few arguments in ccall compared to argument types

########################################
# Error: ccall with too many arguments
ccall(:strlen, Csize_t, (Cstring,), "asdfg", "blah")
#---------------------
LoweringError:
ccall(:strlen, Csize_t, (Cstring,), "asdfg", "blah")
└──────────────────────────────────────────────────┘ ── More arguments than types in ccall

########################################
# Error: ccall varargs with too few args
ccall(:foo, Csize_t, (Cstring...,), "asdfg")
#---------------------
LoweringError:
ccall(:foo, Csize_t, (Cstring...,), "asdfg")
#                     └────────┘ ── C ABI prohibits vararg without one required argument

########################################
# Error: ccall with multiple varargs
ccall(:foo, Csize_t, (Cstring..., Cstring...), "asdfg", "blah")
#---------------------
LoweringError:
ccall(:foo, Csize_t, (Cstring..., Cstring...), "asdfg", "blah")
#                     └────────┘ ── only the trailing ccall argument type should have `...`

