########################################
# where expression without type bounds
A where X
#---------------------
1   (call core.TypeVar :X)
2   (= slot₁/X %₁)
3   slot₁/X
4   TestMod.A
5   (call core.UnionAll %₃ %₄)
6   (return %₅)

########################################
# where expression with upper bound
A where X <: UB
#---------------------
1   TestMod.UB
2   (call core.TypeVar :X %₁)
3   (= slot₁/X %₂)
4   slot₁/X
5   TestMod.A
6   (call core.UnionAll %₄ %₅)
7   (return %₆)

########################################
# where expression with lower bound
A where X >: LB
#---------------------
1   TestMod.X
2   (call core.TypeVar :LB %₁ core.Any)
3   (= slot₁/LB %₂)
4   slot₁/LB
5   TestMod.A
6   (call core.UnionAll %₄ %₅)
7   (return %₆)

########################################
# where expression with both bounds
A where LB <: X <: UB
#---------------------
1   TestMod.LB
2   TestMod.UB
3   (call core.TypeVar :X %₁ %₂)
4   (= slot₁/X %₃)
5   slot₁/X
6   TestMod.A
7   (call core.UnionAll %₅ %₆)
8   (return %₇)

########################################
# where expression with braces
A where {X, Y<:X}
#---------------------
1   (call core.TypeVar :X)
2   (= slot₁/X %₁)
3   slot₁/X
4   slot₁/X
5   (call core.TypeVar :Y %₄)
6   (= slot₂/Y %₅)
7   slot₂/Y
8   TestMod.A
9   (call core.UnionAll %₇ %₈)
10  (call core.UnionAll %₃ %₉)
11  (return %₁₀)

########################################
# Equivalent nested where expression without braces
A where Y<:X where X
#---------------------
1   (call core.TypeVar :X)
2   (= slot₁/X %₁)
3   slot₁/X
4   slot₁/X
5   (call core.TypeVar :Y %₄)
6   (= slot₂/Y %₅)
7   slot₂/Y
8   TestMod.A
9   (call core.UnionAll %₇ %₈)
10  (call core.UnionAll %₃ %₉)
11  (return %₁₀)

########################################
# Error: bad type bounds
A where f()
#---------------------
LoweringError:
A where f()
#       └─┘ ── expected type name or type bounds

########################################
# Error: bad type bounds
A where X < Y < Z
#---------------------
LoweringError:
A where X < Y < Z
#       └───────┘ ── invalid type bounds

########################################
# Error: bad type bounds
A where X <: f() <: Z
#---------------------
LoweringError:
A where X <: f() <: Z
#            └─┘ ── expected type name

########################################
# Error: bad type bounds
A where f() <: Y
#---------------------
LoweringError:
A where f() <: Y
#       └─┘ ── expected type name

########################################
# Error: bad type bounds
A where Y >: f()
#---------------------
LoweringError:
A where Y >: f()
#            └─┘ ── expected type name

########################################
# Simple type application
X{A,B,C}
#---------------------
1   TestMod.X
2   TestMod.A
3   TestMod.B
4   TestMod.C
5   (call core.apply_type %₁ %₂ %₃ %₄)
6   (return %₅)

########################################
# Type with implicit where param upper bound
X{<:A}
#---------------------
1   TestMod.A
2   (call core.TypeVar :#T1 %₁)
3   TestMod.X
4   (call core.apply_type %₃ %₂)
5   (call core.UnionAll %₂ %₄)
6   (return %₅)

########################################
# Type with implicit where param lower bound
X{>:A}
#---------------------
1   TestMod.A
2   (call core.TypeVar :#T1 %₁ core.Any)
3   TestMod.X
4   (call core.apply_type %₃ %₂)
5   (call core.UnionAll %₂ %₄)
6   (return %₅)

########################################
# Type with several implicit where params
X{S, <:A, T, >:B}
#---------------------
1   TestMod.A
2   (call core.TypeVar :#T1 %₁)
3   TestMod.B
4   (call core.TypeVar :#T2 %₃ core.Any)
5   TestMod.X
6   TestMod.S
7   TestMod.T
8   (call core.apply_type %₅ %₆ %₂ %₇ %₄)
9   (call core.UnionAll %₄ %₈)
10  (call core.UnionAll %₂ %₉)
11  (return %₁₀)

########################################
# Error: parameters in type application
X{S, T; W}
#---------------------
LoweringError:
X{S, T; W}
#     └─┘ ── unexpected semicolon in type parameter list

########################################
# Error: assignment in type application
X{S, T=w}
#---------------------
LoweringError:
X{S, T=w}
#   └──┘ ── misplace assignment in type parameter list

########################################
# Simple abstract type definition
abstract type A end
#---------------------
1   (call core.svec)
2   (call core._abstracttype TestMod :A %₁)
3   (= slot₁/A %₂)
4   (call core._setsuper! %₂ core.Any)
5   (call core._typebody! %₂)
6   (global TestMod.A)
7   (const TestMod.A)
8   (isdefined TestMod.A)
9   (gotoifnot %₈ label₁₄)
10  TestMod.A
11  (call core._equiv_typedef %₁₀ %₂)
12  (gotoifnot %₁₁ label₁₄)
13  (goto label₁₅)
14  (= TestMod.A %₂)
15  (return core.nothing)

########################################
# Abstract type definition with supertype
abstract type A <: B end
#---------------------
1   (call core.svec)
2   (call core._abstracttype TestMod :A %₁)
3   (= slot₁/A %₂)
4   TestMod.B
5   (call core._setsuper! %₂ %₄)
6   (call core._typebody! %₂)
7   (global TestMod.A)
8   (const TestMod.A)
9   (isdefined TestMod.A)
10  (gotoifnot %₉ label₁₅)
11  TestMod.A
12  (call core._equiv_typedef %₁₁ %₂)
13  (gotoifnot %₁₂ label₁₅)
14  (goto label₁₆)
15  (= TestMod.A %₂)
16  (return core.nothing)

########################################
# Abstract type definition with multiple typevars
abstract type A{X, Y <: X} end
#---------------------
1   (= slot₂/X (call core.TypeVar :X))
2   slot₂/X
3   (= slot₃/Y (call core.TypeVar :Y %₂))
4   slot₂/X
5   slot₃/Y
6   (call core.svec %₄ %₅)
7   (call core._abstracttype TestMod :A %₆)
8   (= slot₁/A %₇)
9   (call core._setsuper! %₇ core.Any)
10  (call core._typebody! %₇)
11  (global TestMod.A)
12  (const TestMod.A)
13  (isdefined TestMod.A)
14  (gotoifnot %₁₃ label₁₉)
15  TestMod.A
16  (call core._equiv_typedef %₁₅ %₇)
17  (gotoifnot %₁₆ label₁₉)
18  (goto label₂₀)
19  (= TestMod.A %₇)
20  (return core.nothing)

########################################
# Error: Abstract type definition with bad signature
abstract type A() end
#---------------------
LoweringError:
abstract type A() end
#             └─┘ ── invalid type signature

########################################
# Error: Abstract type definition with bad signature
abstract type A(){T} end
#---------------------
LoweringError:
abstract type A(){T} end
#             └────┘ ── invalid type signature

########################################
# Error: Abstract type definition with bad signature
abstract type A() <: B end
#---------------------
LoweringError:
abstract type A() <: B end
#            └───────┘ ── invalid type signature

########################################
# Error: Abstract type definition in function scope
function f()
    abstract type A end
end
#---------------------
LoweringError:
function f()
    abstract type A end
#   └─────────────────┘ ── this syntax is only allowed in top level code
end

########################################
# Simple primitive type definition
primitive type P 8 end
#---------------------
1   (call core.svec)
2   (call core._primitivetype TestMod :P %₁ 8)
3   (= slot₁/P %₂)
4   (call core._setsuper! %₂ core.Any)
5   (call core._typebody! %₂)
6   (global TestMod.P)
7   (const TestMod.P)
8   (isdefined TestMod.P)
9   (gotoifnot %₈ label₁₄)
10  TestMod.P
11  (call core._equiv_typedef %₁₀ %₂)
12  (gotoifnot %₁₁ label₁₄)
13  (goto label₁₅)
14  (= TestMod.P %₂)
15  (return core.nothing)

########################################
# Complex primitive type definition
primitive type P{X,Y} <: Z 32 end
#---------------------
1   (= slot₂/X (call core.TypeVar :X))
2   (= slot₃/Y (call core.TypeVar :Y))
3   slot₂/X
4   slot₃/Y
5   (call core.svec %₃ %₄)
6   (call core._primitivetype TestMod :P %₅ 32)
7   (= slot₁/P %₆)
8   TestMod.Z
9   (call core._setsuper! %₆ %₈)
10  (call core._typebody! %₆)
11  (global TestMod.P)
12  (const TestMod.P)
13  (isdefined TestMod.P)
14  (gotoifnot %₁₃ label₁₉)
15  TestMod.P
16  (call core._equiv_typedef %₁₅ %₆)
17  (gotoifnot %₁₆ label₁₉)
18  (goto label₂₀)
19  (= TestMod.P %₆)
20  (return core.nothing)

########################################
# Primitive type definition with computed size (should this be allowed??)
primitive type P P_nbits() end
#---------------------
1   (call core.svec)
2   TestMod.P_nbits
3   (call %₂)
4   (call core._primitivetype TestMod :P %₁ %₃)
5   (= slot₁/P %₄)
6   (call core._setsuper! %₄ core.Any)
7   (call core._typebody! %₄)
8   (global TestMod.P)
9   (const TestMod.P)
10  (isdefined TestMod.P)
11  (gotoifnot %₁₀ label₁₆)
12  TestMod.P
13  (call core._equiv_typedef %₁₂ %₄)
14  (gotoifnot %₁₃ label₁₆)
15  (goto label₁₇)
16  (= TestMod.P %₄)
17  (return core.nothing)

########################################
# Empty struct
struct X
end
#---------------------
1   (global TestMod.X)
2   (const TestMod.X)
3   (call core.svec)
4   (call core.svec)
5   (call core.svec)
6   (call core._structtype TestMod :X %₃ %₄ %₅ false 0)
7   (= slot₁/X %₆)
8   (call core._setsuper! %₆ core.Any)
9   (isdefined TestMod.X)
10  (gotoifnot %₉ label₂₀)
11  TestMod.X
12  (call core._equiv_typedef %₁₁ %₆)
13  (gotoifnot %₁₂ label₁₇)
14  TestMod.X
15  (= slot₁/X %₁₄)
16  (goto label₁₉)
17  slot₁/X
18  (= TestMod.X %₁₇)
19  (goto label₂₂)
20  slot₁/X
21  (= TestMod.X %₂₀)
22  slot₁/X
23  (call core.svec)
24  (call core._typebody! %₂₂ %₂₃)
25  TestMod.X
26  (call core.apply_type core.Type %₂₅)
27  (call core.svec %₂₆)
28  (call core.svec)
29  SourceLocation::1:1
30  (call core.svec %₂₇ %₂₈ %₂₉)
31  --- method core.nothing %₃₀
    slots: [slot₁/#self#(!read)]
    1   TestMod.X
    2   (new %₁)
    3   (return %₂)
32  (return core.nothing)

########################################
# Basic struct
struct X
    a
    b::T
    c
end
#---------------------
1   (global TestMod.X)
2   (const TestMod.X)
3   (call core.svec)
4   (call core.svec :a :b :c)
5   (call core.svec)
6   (call core._structtype TestMod :X %₃ %₄ %₅ false 3)
7   (= slot₁/X %₆)
8   (call core._setsuper! %₆ core.Any)
9   (isdefined TestMod.X)
10  (gotoifnot %₉ label₂₀)
11  TestMod.X
12  (call core._equiv_typedef %₁₁ %₆)
13  (gotoifnot %₁₂ label₁₇)
14  TestMod.X
15  (= slot₁/X %₁₄)
16  (goto label₁₉)
17  slot₁/X
18  (= TestMod.X %₁₇)
19  (goto label₂₂)
20  slot₁/X
21  (= TestMod.X %₂₀)
22  slot₁/X
23  TestMod.T
24  (call core.svec core.Any %₂₃ core.Any)
25  (call core._typebody! %₂₂ %₂₄)
26  TestMod.T
27  (call core.=== core.Any %₂₆)
28  (gotoifnot %₂₇ label₃₀)
29  (goto label₃₇)
30  TestMod.X
31  (call core.apply_type core.Type %₃₀)
32  (call core.svec %₃₁ core.Any core.Any core.Any)
33  (call core.svec)
34  SourceLocation::1:1
35  (call core.svec %₃₂ %₃₃ %₃₄)
36  --- method core.nothing %₃₅
    slots: [slot₁/#ctor-self# slot₂/a slot₃/b slot₄/c slot₅/tmp]
    1   (call core.fieldtype slot₁/#ctor-self# 2)
    2   slot₃/b
    3   (= slot₅/tmp %₂)
    4   slot₅/tmp
    5   (call core.isa %₄ %₁)
    6   (gotoifnot %₅ label₈)
    7   (goto label₁₀)
    8   slot₅/tmp
    9   (= slot₅/tmp (call top.convert %₁ %₈))
    10  slot₅/tmp
    11  (new slot₁/#ctor-self# slot₂/a %₁₀ slot₄/c)
    12  (return %₁₁)
37  TestMod.X
38  (call core.apply_type core.Type %₃₇)
39  TestMod.T
40  (call core.svec %₃₈ core.Any %₃₉ core.Any)
41  (call core.svec)
42  SourceLocation::1:1
43  (call core.svec %₄₀ %₄₁ %₄₂)
44  --- method core.nothing %₄₃
    slots: [slot₁/#self#(!read) slot₂/a slot₃/b slot₄/c]
    1   TestMod.X
    2   (new %₁ slot₂/a slot₃/b slot₄/c)
    3   (return %₂)
45  (return core.nothing)

########################################
# Struct with supertype and type params
struct X{U, S <: V <: T} <: Z
end
#---------------------
1   (global TestMod.X)
2   (const TestMod.X)
3   (= slot₂/U (call core.TypeVar :U))
4   TestMod.S
5   TestMod.T
6   (= slot₃/V (call core.TypeVar :V %₄ %₅))
7   slot₂/U
8   slot₃/V
9   (call core.svec %₇ %₈)
10  (call core.svec)
11  (call core.svec)
12  (call core._structtype TestMod :X %₉ %₁₀ %₁₁ false 0)
13  (= slot₄/X %₁₂)
14  TestMod.Z
15  (call core._setsuper! %₁₂ %₁₄)
16  (isdefined TestMod.X)
17  (gotoifnot %₁₆ label₃₇)
18  TestMod.X
19  (call core._equiv_typedef %₁₈ %₁₂)
20  (gotoifnot %₁₉ label₃₄)
21  TestMod.X
22  (= slot₄/X %₂₁)
23  TestMod.X
24  (call top.getproperty %₂₃ :body)
25  (call top.getproperty %₂₄ :body)
26  (call top.getproperty %₂₅ :parameters)
27  (call top.indexed_iterate %₂₆ 1)
28  (= slot₂/U (call core.getfield %₂₇ 1))
29  (= slot₁/iterstate (call core.getfield %₂₇ 2))
30  slot₁/iterstate
31  (call top.indexed_iterate %₂₆ 2 %₃₀)
32  (= slot₃/V (call core.getfield %₃₁ 1))
33  (goto label₃₆)
34  slot₄/X
35  (= TestMod.X %₃₄)
36  (goto label₃₉)
37  slot₄/X
38  (= TestMod.X %₃₇)
39  slot₄/X
40  (call core.svec)
41  (call core._typebody! %₃₉ %₄₀)
42  slot₂/U
43  slot₃/V
44  TestMod.X
45  slot₂/U
46  slot₃/V
47  (call core.apply_type %₄₄ %₄₅ %₄₆)
48  (call core.apply_type core.Type %₄₇)
49  (call core.UnionAll %₄₃ %₄₈)
50  (call core.UnionAll %₄₂ %₄₉)
51  (call core.svec %₅₀)
52  (call core.svec)
53  SourceLocation::1:1
54  (call core.svec %₅₁ %₅₂ %₅₃)
55  --- method core.nothing %₅₄
    slots: [slot₁/#ctor-self#]
    1   (new slot₁/#ctor-self#)
    2   (return %₁)
56  (return core.nothing)

########################################
# Struct with const and atomic fields
struct X
    const a
    @atomic b
    const @atomic c
end
#---------------------
1   (global TestMod.X)
2   (const TestMod.X)
3   (call core.svec)
4   (call core.svec :a :b :c)
5   (call core.svec 1 :const 2 :atomic 3 :atomic 3 :const)
6   (call core._structtype TestMod :X %₃ %₄ %₅ false 3)
7   (= slot₁/X %₆)
8   (call core._setsuper! %₆ core.Any)
9   (isdefined TestMod.X)
10  (gotoifnot %₉ label₂₀)
11  TestMod.X
12  (call core._equiv_typedef %₁₁ %₆)
13  (gotoifnot %₁₂ label₁₇)
14  TestMod.X
15  (= slot₁/X %₁₄)
16  (goto label₁₉)
17  slot₁/X
18  (= TestMod.X %₁₇)
19  (goto label₂₂)
20  slot₁/X
21  (= TestMod.X %₂₀)
22  slot₁/X
23  (call core.svec core.Any core.Any core.Any)
24  (call core._typebody! %₂₂ %₂₃)
25  TestMod.X
26  (call core.apply_type core.Type %₂₅)
27  (call core.svec %₂₆ core.Any core.Any core.Any)
28  (call core.svec)
29  SourceLocation::1:1
30  (call core.svec %₂₇ %₂₈ %₂₉)
31  --- method core.nothing %₃₀
    slots: [slot₁/#self#(!read) slot₂/a slot₃/b slot₄/c]
    1   TestMod.X
    2   (new %₁ slot₂/a slot₃/b slot₄/c)
    3   (return %₂)
32  (return core.nothing)

########################################
# Documented struct
"""
X docs
"""
struct X
    "field a docs"
    a
    "field b docs"
    b
end
#---------------------
1   (global TestMod.X)
2   (const TestMod.X)
3   (call core.svec)
4   (call core.svec :a :b)
5   (call core.svec)
6   (call core._structtype TestMod :X %₃ %₄ %₅ false 2)
7   (= slot₁/X %₆)
8   (call core._setsuper! %₆ core.Any)
9   (isdefined TestMod.X)
10  (gotoifnot %₉ label₂₀)
11  TestMod.X
12  (call core._equiv_typedef %₁₁ %₆)
13  (gotoifnot %₁₂ label₁₇)
14  TestMod.X
15  (= slot₁/X %₁₄)
16  (goto label₁₉)
17  slot₁/X
18  (= TestMod.X %₁₇)
19  (goto label₂₂)
20  slot₁/X
21  (= TestMod.X %₂₀)
22  slot₁/X
23  (call core.svec core.Any core.Any)
24  (call core._typebody! %₂₂ %₂₃)
25  TestMod.X
26  (call core.apply_type core.Type %₂₅)
27  (call core.svec %₂₆ core.Any core.Any)
28  (call core.svec)
29  SourceLocation::4:1
30  (call core.svec %₂₇ %₂₈ %₂₉)
31  --- method core.nothing %₃₀
    slots: [slot₁/#self#(!read) slot₂/a slot₃/b]
    1   TestMod.X
    2   (new %₁ slot₂/a slot₃/b)
    3   (return %₂)
32  JuliaLowering.bind_docs!
33  (call core.tuple :field_docs)
34  (call core.apply_type core.NamedTuple %₃₃)
35  (call core.svec 1 "field a docs" 2 "field b docs")
36  (call core.tuple %₃₅)
37  (call %₃₄ %₃₆)
38  TestMod.X
39  SourceLocation::4:1
40  (call core.kwcall %₃₇ %₃₂ %₃₈ "X docs\n" %₃₉)
41  (return core.nothing)

########################################
# Struct with outer constructor
struct X{U}
    x::U
end
#---------------------
1   (global TestMod.X)
2   (const TestMod.X)
3   (= slot₁/U (call core.TypeVar :U))
4   slot₁/U
5   (call core.svec %₄)
6   (call core.svec :x)
7   (call core.svec)
8   (call core._structtype TestMod :X %₅ %₆ %₇ false 1)
9   (= slot₂/X %₈)
10  (call core._setsuper! %₈ core.Any)
11  (isdefined TestMod.X)
12  (gotoifnot %₁₁ label₂₇)
13  TestMod.X
14  (call core._equiv_typedef %₁₃ %₈)
15  (gotoifnot %₁₄ label₂₄)
16  TestMod.X
17  (= slot₂/X %₁₆)
18  TestMod.X
19  (call top.getproperty %₁₈ :body)
20  (call top.getproperty %₁₉ :parameters)
21  (call top.indexed_iterate %₂₀ 1)
22  (= slot₁/U (call core.getfield %₂₁ 1))
23  (goto label₂₆)
24  slot₂/X
25  (= TestMod.X %₂₄)
26  (goto label₂₉)
27  slot₂/X
28  (= TestMod.X %₂₇)
29  slot₂/X
30  slot₁/U
31  (call core.svec %₃₀)
32  (call core._typebody! %₂₉ %₃₁)
33  slot₁/U
34  TestMod.X
35  slot₁/U
36  (call core.apply_type %₃₄ %₃₅)
37  (call core.apply_type core.Type %₃₆)
38  (call core.UnionAll %₃₃ %₃₇)
39  (call core.svec %₃₈ core.Any)
40  (call core.svec)
41  SourceLocation::1:1
42  (call core.svec %₃₉ %₄₀ %₄₁)
43  --- method core.nothing %₄₂
    slots: [slot₁/#ctor-self# slot₂/x slot₃/tmp]
    1   (call core.fieldtype slot₁/#ctor-self# 1)
    2   slot₂/x
    3   (= slot₃/tmp %₂)
    4   slot₃/tmp
    5   (call core.isa %₄ %₁)
    6   (gotoifnot %₅ label₈)
    7   (goto label₁₀)
    8   slot₃/tmp
    9   (= slot₃/tmp (call top.convert %₁ %₈))
    10  slot₃/tmp
    11  (new slot₁/#ctor-self# %₁₀)
    12  (return %₁₁)
44  TestMod.X
45  (call core.apply_type core.Type %₄₄)
46  slot₁/U
47  (call core.svec %₄₅ %₄₆)
48  slot₁/U
49  (call core.svec %₄₈)
50  SourceLocation::1:1
51  (call core.svec %₄₇ %₄₉ %₅₀)
52  --- method core.nothing %₅₁
    slots: [slot₁/#self#(!read) slot₂/x]
    1   TestMod.X
    2   static_parameter₁
    3   (call core.apply_type %₁ %₂)
    4   (new %₃ slot₂/x)
    5   (return %₄)
53  (return core.nothing)

########################################
# Struct with outer constructor where one typevar is constrained by the other
# See https://github.com/JuliaLang/julia/issues/27269)
struct X{T, S <: Vector{T}}
    v::Vector{S}
end
#---------------------
1   (global TestMod.X)
2   (const TestMod.X)
3   (= slot₃/T (call core.TypeVar :T))
4   TestMod.Vector
5   slot₃/T
6   (call core.apply_type %₄ %₅)
7   (= slot₂/S (call core.TypeVar :S %₆))
8   slot₃/T
9   slot₂/S
10  (call core.svec %₈ %₉)
11  (call core.svec :v)
12  (call core.svec)
13  (call core._structtype TestMod :X %₁₀ %₁₁ %₁₂ false 1)
14  (= slot₄/X %₁₃)
15  (call core._setsuper! %₁₃ core.Any)
16  (isdefined TestMod.X)
17  (gotoifnot %₁₆ label₃₇)
18  TestMod.X
19  (call core._equiv_typedef %₁₈ %₁₃)
20  (gotoifnot %₁₉ label₃₄)
21  TestMod.X
22  (= slot₄/X %₂₁)
23  TestMod.X
24  (call top.getproperty %₂₃ :body)
25  (call top.getproperty %₂₄ :body)
26  (call top.getproperty %₂₅ :parameters)
27  (call top.indexed_iterate %₂₆ 1)
28  (= slot₃/T (call core.getfield %₂₇ 1))
29  (= slot₁/iterstate (call core.getfield %₂₇ 2))
30  slot₁/iterstate
31  (call top.indexed_iterate %₂₆ 2 %₃₀)
32  (= slot₂/S (call core.getfield %₃₁ 1))
33  (goto label₃₆)
34  slot₄/X
35  (= TestMod.X %₃₄)
36  (goto label₃₉)
37  slot₄/X
38  (= TestMod.X %₃₇)
39  slot₄/X
40  TestMod.Vector
41  slot₂/S
42  (call core.apply_type %₄₀ %₄₁)
43  (call core.svec %₄₂)
44  (call core._typebody! %₃₉ %₄₃)
45  slot₃/T
46  slot₂/S
47  TestMod.X
48  slot₃/T
49  slot₂/S
50  (call core.apply_type %₄₇ %₄₈ %₄₉)
51  (call core.apply_type core.Type %₅₀)
52  (call core.UnionAll %₄₆ %₅₁)
53  (call core.UnionAll %₄₅ %₅₂)
54  (call core.svec %₅₃ core.Any)
55  (call core.svec)
56  SourceLocation::1:1
57  (call core.svec %₅₄ %₅₅ %₅₆)
58  --- method core.nothing %₅₇
    slots: [slot₁/#ctor-self# slot₂/v slot₃/tmp]
    1   (call core.fieldtype slot₁/#ctor-self# 1)
    2   slot₂/v
    3   (= slot₃/tmp %₂)
    4   slot₃/tmp
    5   (call core.isa %₄ %₁)
    6   (gotoifnot %₅ label₈)
    7   (goto label₁₀)
    8   slot₃/tmp
    9   (= slot₃/tmp (call top.convert %₁ %₈))
    10  slot₃/tmp
    11  (new slot₁/#ctor-self# %₁₀)
    12  (return %₁₁)
59  TestMod.X
60  (call core.apply_type core.Type %₅₉)
61  TestMod.Vector
62  slot₂/S
63  (call core.apply_type %₆₁ %₆₂)
64  (call core.svec %₆₀ %₆₃)
65  slot₃/T
66  slot₂/S
67  (call core.svec %₆₅ %₆₆)
68  SourceLocation::1:1
69  (call core.svec %₆₄ %₆₇ %₆₈)
70  --- method core.nothing %₆₉
    slots: [slot₁/#self#(!read) slot₂/v]
    1   TestMod.X
    2   static_parameter₁
    3   static_parameter₂
    4   (call core.apply_type %₁ %₂ %₃)
    5   (new %₄ slot₂/v)
    6   (return %₅)
71  (return core.nothing)

########################################
# User defined inner constructors and helper functions for structs without type params
struct X
    x
    f() = new(1)
    #X() = f() # FIXME: this X() captures `f` (in flisp, as a Box :-/ )
    X(x) = new(x)
    X(y,z)::ReallyXIPromise = new(y+z)
    """
    Docs for X constructor
    """
    X(a,b,c) = new(a)
end
#---------------------
1   (call core.svec)
2   (call core.svec)
3   (call JuliaLowering.eval_closure_type TestMod :#f##0 %₁ %₂)
4   TestMod.#f##0
5   (call core.svec %₄)
6   (call core.svec)
7   SourceLocation::3:5
8   (call core.svec %₅ %₆ %₇)
9   --- method core.nothing %₈
    slots: [slot₁/#self#(!read)]
    1   TestMod.X
    2   (new %₁ 1)
    3   (return %₂)
10  (newvar slot₂/f)
11  (global TestMod.X)
12  (const TestMod.X)
13  (call core.svec)
14  (call core.svec :x)
15  (call core.svec)
16  (call core._structtype TestMod :X %₁₃ %₁₄ %₁₅ false 1)
17  (= slot₁/X %₁₆)
18  (call core._setsuper! %₁₆ core.Any)
19  (isdefined TestMod.X)
20  (gotoifnot %₁₉ label₃₀)
21  TestMod.X
22  (call core._equiv_typedef %₂₁ %₁₆)
23  (gotoifnot %₂₂ label₂₇)
24  TestMod.X
25  (= slot₁/X %₂₄)
26  (goto label₂₉)
27  slot₁/X
28  (= TestMod.X %₂₇)
29  (goto label₃₂)
30  slot₁/X
31  (= TestMod.X %₃₀)
32  slot₁/X
33  (call core.svec core.Any)
34  (call core._typebody! %₃₂ %₃₃)
35  TestMod.#f##0
36  (new %₃₅)
37  (= slot₂/f %₃₆)
38  TestMod.X
39  (call core.apply_type core.Type %₃₈)
40  (call core.svec %₃₉ core.Any)
41  (call core.svec)
42  SourceLocation::5:5
43  (call core.svec %₄₀ %₄₁ %₄₂)
44  --- method core.nothing %₄₃
    slots: [slot₁/#ctor-self# slot₂/x]
    1   slot₁/#ctor-self#
    2   (new %₁ slot₂/x)
    3   (return %₂)
45  TestMod.X
46  (call core.apply_type core.Type %₄₅)
47  (call core.svec %₄₆ core.Any core.Any)
48  (call core.svec)
49  SourceLocation::6:5
50  (call core.svec %₄₇ %₄₈ %₄₉)
51  --- method core.nothing %₅₀
    slots: [slot₁/#ctor-self# slot₂/y slot₃/z slot₄/tmp(!read)]
    1   TestMod.ReallyXIPromise
    2   slot₁/#ctor-self#
    3   TestMod.+
    4   (call %₃ slot₂/y slot₃/z)
    5   (= slot₄/tmp (new %₂ %₄))
    6   slot₄/tmp
    7   (call core.isa %₆ %₁)
    8   (gotoifnot %₇ label₁₀)
    9   (goto label₁₃)
    10  slot₄/tmp
    11  (call top.convert %₁ %₁₀)
    12  (= slot₄/tmp (call core.typeassert %₁₁ %₁))
    13  slot₄/tmp
    14  (return %₁₃)
52  TestMod.X
53  (call core.apply_type core.Type %₅₂)
54  (call core.svec %₅₃ core.Any core.Any core.Any)
55  (call core.svec)
56  SourceLocation::10:5
57  (call core.svec %₅₄ %₅₅ %₅₆)
58  --- method core.nothing %₅₇
    slots: [slot₁/#ctor-self# slot₂/a slot₃/b(!read) slot₄/c(!read)]
    1   slot₁/#ctor-self#
    2   (new %₁ slot₂/a)
    3   (return %₂)
59  TestMod.X
60  (call core.apply_type core.Type %₅₉)
61  (call JuliaLowering.bind_docs! %₆₀ "Docs for X constructor\n" %₅₇)
62  (return core.nothing)

########################################
# User defined inner constructors and helper functions for structs with type params
struct X{S,T}
    x
    X{A,B}() = new(1)
    X{U,V}() where {U,V} = new(1)
    f() = new{A,B}(1)
end
#---------------------
1   (call core.svec)
2   (call core.svec)
3   (call JuliaLowering.eval_closure_type TestMod :#f##1 %₁ %₂)
4   TestMod.#f##1
5   (call core.svec %₄)
6   (call core.svec)
7   SourceLocation::5:5
8   (call core.svec %₅ %₆ %₇)
9   --- method core.nothing %₈
    slots: [slot₁/#self#(!read)]
    1   TestMod.X
    2   TestMod.A
    3   TestMod.B
    4   (call core.apply_type %₁ %₂ %₃)
    5   (new %₄ 1)
    6   (return %₅)
10  (newvar slot₅/f)
11  (global TestMod.X)
12  (const TestMod.X)
13  (= slot₂/S (call core.TypeVar :S))
14  (= slot₃/T (call core.TypeVar :T))
15  slot₂/S
16  slot₃/T
17  (call core.svec %₁₅ %₁₆)
18  (call core.svec :x)
19  (call core.svec)
20  (call core._structtype TestMod :X %₁₇ %₁₈ %₁₉ false 1)
21  (= slot₄/X %₂₀)
22  (call core._setsuper! %₂₀ core.Any)
23  (isdefined TestMod.X)
24  (gotoifnot %₂₃ label₄₄)
25  TestMod.X
26  (call core._equiv_typedef %₂₅ %₂₀)
27  (gotoifnot %₂₆ label₄₁)
28  TestMod.X
29  (= slot₄/X %₂₈)
30  TestMod.X
31  (call top.getproperty %₃₀ :body)
32  (call top.getproperty %₃₁ :body)
33  (call top.getproperty %₃₂ :parameters)
34  (call top.indexed_iterate %₃₃ 1)
35  (= slot₂/S (call core.getfield %₃₄ 1))
36  (= slot₁/iterstate (call core.getfield %₃₄ 2))
37  slot₁/iterstate
38  (call top.indexed_iterate %₃₃ 2 %₃₇)
39  (= slot₃/T (call core.getfield %₃₈ 1))
40  (goto label₄₃)
41  slot₄/X
42  (= TestMod.X %₄₁)
43  (goto label₄₆)
44  slot₄/X
45  (= TestMod.X %₄₄)
46  slot₄/X
47  (call core.svec core.Any)
48  (call core._typebody! %₄₆ %₄₇)
49  TestMod.X
50  TestMod.A
51  TestMod.B
52  (call core.apply_type %₄₉ %₅₀ %₅₁)
53  (call core.apply_type core.Type %₅₂)
54  (call core.svec %₅₃)
55  (call core.svec)
56  SourceLocation::3:5
57  (call core.svec %₅₄ %₅₅ %₅₆)
58  --- method core.nothing %₅₇
    slots: [slot₁/#ctor-self#]
    1   slot₁/#ctor-self#
    2   (new %₁ 1)
    3   (return %₂)
59  (= slot₆/U (call core.TypeVar :U))
60  (= slot₇/V (call core.TypeVar :V))
61  TestMod.X
62  slot₆/U
63  slot₇/V
64  (call core.apply_type %₆₁ %₆₂ %₆₃)
65  (call core.apply_type core.Type %₆₄)
66  (call core.svec %₆₅)
67  slot₆/U
68  slot₇/V
69  (call core.svec %₆₇ %₆₈)
70  SourceLocation::4:5
71  (call core.svec %₆₆ %₆₉ %₇₀)
72  --- method core.nothing %₇₁
    slots: [slot₁/#ctor-self#]
    1   slot₁/#ctor-self#
    2   (new %₁ 1)
    3   (return %₂)
73  TestMod.#f##1
74  (new %₇₃)
75  (= slot₅/f %₇₄)
76  (return core.nothing)

########################################
# new() calls with splats; `Any` fields
struct X
    x
    y
    X(xs) = new(xs...)
end
#---------------------
1   (global TestMod.X)
2   (const TestMod.X)
3   (call core.svec)
4   (call core.svec :x :y)
5   (call core.svec)
6   (call core._structtype TestMod :X %₃ %₄ %₅ false 2)
7   (= slot₁/X %₆)
8   (call core._setsuper! %₆ core.Any)
9   (isdefined TestMod.X)
10  (gotoifnot %₉ label₂₀)
11  TestMod.X
12  (call core._equiv_typedef %₁₁ %₆)
13  (gotoifnot %₁₂ label₁₇)
14  TestMod.X
15  (= slot₁/X %₁₄)
16  (goto label₁₉)
17  slot₁/X
18  (= TestMod.X %₁₇)
19  (goto label₂₂)
20  slot₁/X
21  (= TestMod.X %₂₀)
22  slot₁/X
23  (call core.svec core.Any core.Any)
24  (call core._typebody! %₂₂ %₂₃)
25  TestMod.X
26  (call core.apply_type core.Type %₂₅)
27  (call core.svec %₂₆ core.Any)
28  (call core.svec)
29  SourceLocation::4:5
30  (call core.svec %₂₇ %₂₈ %₂₉)
31  --- method core.nothing %₃₀
    slots: [slot₁/#ctor-self# slot₂/xs]
    1   slot₁/#ctor-self#
    2   (call core._apply_iterate top.iterate core.tuple slot₂/xs)
    3   (splatnew %₁ %₂)
    4   (return %₃)
32  (return core.nothing)

########################################
# new() calls with splats; typed fields
struct X{T}
    x::T
    y::A
    X{T}(xs) where {T} = new(xs...)
end
#---------------------
1   (global TestMod.X)
2   (const TestMod.X)
3   (= slot₁/T (call core.TypeVar :T))
4   slot₁/T
5   (call core.svec %₄)
6   (call core.svec :x :y)
7   (call core.svec)
8   (call core._structtype TestMod :X %₅ %₆ %₇ false 2)
9   (= slot₂/X %₈)
10  (call core._setsuper! %₈ core.Any)
11  (isdefined TestMod.X)
12  (gotoifnot %₁₁ label₂₇)
13  TestMod.X
14  (call core._equiv_typedef %₁₃ %₈)
15  (gotoifnot %₁₄ label₂₄)
16  TestMod.X
17  (= slot₂/X %₁₆)
18  TestMod.X
19  (call top.getproperty %₁₈ :body)
20  (call top.getproperty %₁₉ :parameters)
21  (call top.indexed_iterate %₂₀ 1)
22  (= slot₁/T (call core.getfield %₂₁ 1))
23  (goto label₂₆)
24  slot₂/X
25  (= TestMod.X %₂₄)
26  (goto label₂₉)
27  slot₂/X
28  (= TestMod.X %₂₇)
29  slot₂/X
30  slot₁/T
31  TestMod.A
32  (call core.svec %₃₀ %₃₁)
33  (call core._typebody! %₂₉ %₃₂)
34  (= slot₃/T (call core.TypeVar :T))
35  TestMod.X
36  slot₃/T
37  (call core.apply_type %₃₅ %₃₆)
38  (call core.apply_type core.Type %₃₇)
39  (call core.svec %₃₈ core.Any)
40  slot₃/T
41  (call core.svec %₄₀)
42  SourceLocation::4:5
43  (call core.svec %₃₉ %₄₁ %₄₂)
44  --- method core.nothing %₄₃
    slots: [slot₁/#ctor-self# slot₂/xs slot₃/tmp slot₄/tmp]
    1   (call core._apply_iterate top.iterate core.tuple slot₂/xs)
    2   (call core.nfields %₁)
    3   (call top.ult_int %₂ 2)
    4   (gotoifnot %₃ label₇)
    5   (call top.ArgumentError "too few arguments in `new` (expected 2)")
    6   (call core.throw %₅)
    7   (call top.ult_int 2 %₂)
    8   (gotoifnot %₇ label₁₁)
    9   (call top.ArgumentError "too many arguments in `new` (expected 2)")
    10  (call core.throw %₉)
    11  slot₁/#ctor-self#
    12  (call core.fieldtype %₁₁ 1)
    13  (= slot₃/tmp (call core.getfield %₁ 1))
    14  slot₃/tmp
    15  (call core.isa %₁₄ %₁₂)
    16  (gotoifnot %₁₅ label₁₈)
    17  (goto label₂₀)
    18  slot₃/tmp
    19  (= slot₃/tmp (call top.convert %₁₂ %₁₈))
    20  slot₃/tmp
    21  (call core.fieldtype %₁₁ 2)
    22  (= slot₄/tmp (call core.getfield %₁ 2))
    23  slot₄/tmp
    24  (call core.isa %₂₃ %₂₁)
    25  (gotoifnot %₂₄ label₂₇)
    26  (goto label₂₉)
    27  slot₄/tmp
    28  (= slot₄/tmp (call top.convert %₂₁ %₂₇))
    29  slot₄/tmp
    30  (new %₁₁ %₂₀ %₂₉)
    31  (return %₃₀)
45  (return core.nothing)

########################################
# Error: new doesn't accept keywords
struct X
    X() = new(a=1)
end
#---------------------
LoweringError:
struct X
    X() = new(a=1)
#             └─┘ ── `new` does not accept keyword arguments
end

########################################
# Error: new doesn't accept keywords (params block)
struct X
    X() = new(; a=1)
end
#---------------------
LoweringError:
struct X
    X() = new(; a=1)
#             └───┘ ── `new` does not accept keyword arguments
end

########################################
# Error: User defined inner constructors without enough type params
struct X{S,T}
    X() = new{A}()
end
#---------------------
LoweringError:
struct X{S,T}
    X() = new{A}()
#         └────┘ ── too few type parameters specified in `new{...}`
end

########################################
# Error: User defined inner constructors without enough type params
struct X{S,T}
    X{A}() = new()
end
#---------------------
LoweringError:
struct X{S,T}
    X{A}() = new()
#            └─┘ ── too few type parameters specified in `new`
end

########################################
# Error: User defined inner constructors with too many type params
struct X{S,T}
    X() = new{A,B,C}()
end
#---------------------
LoweringError:
struct X{S,T}
    X() = new{A,B,C}()
#         └────────┘ ── too many type parameters specified in `new{...}`
end

########################################
# Error: Struct not at top level
function f()
    struct X
    end
end
#---------------------
LoweringError:
function f()
#   ┌───────
    struct X
    end
#─────┘ ── this syntax is only allowed in top level code
end

