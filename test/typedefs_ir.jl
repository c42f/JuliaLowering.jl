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
5   slot₁/A
6   (call core._typebody! false %₅)
7   (global TestMod.A)
8   (latestworld)
9   (call core.isdefinedglobal TestMod :A false)
10  (gotoifnot %₉ label₁₅)
11  TestMod.A
12  (call core._equiv_typedef %₁₁ %₂)
13  (gotoifnot %₁₂ label₁₅)
14  (goto label₁₆)
15  (constdecl TestMod.A %₂)
16  (latestworld)
17  (return core.nothing)

########################################
# Abstract type definition with supertype
abstract type A <: B end
#---------------------
1   (call core.svec)
2   (call core._abstracttype TestMod :A %₁)
3   (= slot₁/A %₂)
4   TestMod.B
5   (call core._setsuper! %₂ %₄)
6   slot₁/A
7   (call core._typebody! false %₆)
8   (global TestMod.A)
9   (latestworld)
10  (call core.isdefinedglobal TestMod :A false)
11  (gotoifnot %₁₀ label₁₆)
12  TestMod.A
13  (call core._equiv_typedef %₁₂ %₂)
14  (gotoifnot %₁₃ label₁₆)
15  (goto label₁₇)
16  (constdecl TestMod.A %₂)
17  (latestworld)
18  (return core.nothing)

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
10  slot₁/A
11  (call core._typebody! false %₁₀)
12  (global TestMod.A)
13  (latestworld)
14  (call core.isdefinedglobal TestMod :A false)
15  (gotoifnot %₁₄ label₂₀)
16  TestMod.A
17  (call core._equiv_typedef %₁₆ %₇)
18  (gotoifnot %₁₇ label₂₀)
19  (goto label₂₁)
20  (constdecl TestMod.A %₇)
21  (latestworld)
22  (return core.nothing)

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
5   slot₁/P
6   (call core._typebody! false %₅)
7   (global TestMod.P)
8   (latestworld)
9   (call core.isdefinedglobal TestMod :P false)
10  (gotoifnot %₉ label₁₅)
11  TestMod.P
12  (call core._equiv_typedef %₁₁ %₂)
13  (gotoifnot %₁₂ label₁₅)
14  (goto label₁₆)
15  (constdecl TestMod.P %₂)
16  (latestworld)
17  (return core.nothing)

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
10  slot₁/P
11  (call core._typebody! false %₁₀)
12  (global TestMod.P)
13  (latestworld)
14  (call core.isdefinedglobal TestMod :P false)
15  (gotoifnot %₁₄ label₂₀)
16  TestMod.P
17  (call core._equiv_typedef %₁₆ %₆)
18  (gotoifnot %₁₇ label₂₀)
19  (goto label₂₁)
20  (constdecl TestMod.P %₆)
21  (latestworld)
22  (return core.nothing)

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
7   slot₁/P
8   (call core._typebody! false %₇)
9   (global TestMod.P)
10  (latestworld)
11  (call core.isdefinedglobal TestMod :P false)
12  (gotoifnot %₁₁ label₁₇)
13  TestMod.P
14  (call core._equiv_typedef %₁₃ %₄)
15  (gotoifnot %₁₄ label₁₇)
16  (goto label₁₈)
17  (constdecl TestMod.P %₄)
18  (latestworld)
19  (return core.nothing)

########################################
# Empty struct
struct X
end
#---------------------
1   (global TestMod.X)
2   (latestworld)
3   (call core.svec)
4   (call core.svec)
5   (call core.svec)
6   (call core._structtype TestMod :X %₃ %₄ %₅ false 0)
7   (= slot₁/X %₆)
8   (call core._setsuper! %₆ core.Any)
9   (call core.isdefinedglobal TestMod :X false)
10  (gotoifnot %₉ label₁₄)
11  TestMod.X
12  (= slot₂/if_val (call core._equiv_typedef %₁₁ %₆))
13  (goto label₁₅)
14  (= slot₂/if_val false)
15  slot₂/if_val
16  (gotoifnot %₁₅ label₂₀)
17  TestMod.X
18  (= slot₃/if_val %₁₇)
19  (goto label₂₁)
20  (= slot₃/if_val false)
21  slot₃/if_val
22  (gotoifnot %₁₅ label₂₃)
23  (call core.svec)
24  (call core._typebody! %₂₁ %₆ %₂₃)
25  (constdecl TestMod.X %₂₄)
26  (latestworld)
27  (latestworld)
28  TestMod.X
29  (call core.apply_type core.Type %₂₈)
30  (call core.svec %₂₉)
31  (call core.svec)
32  SourceLocation::1:1
33  (call core.svec %₃₀ %₃₁ %₃₂)
34  --- method core.nothing %₃₃
    slots: [slot₁/#self#(!read)]
    1   TestMod.X
    2   (new %₁)
    3   (return %₂)
35  (latestworld)
36  (return core.nothing)

########################################
# Basic struct
struct X
    a
    b::T
    c
end
#---------------------
1   (global TestMod.X)
2   (latestworld)
3   (call core.svec)
4   (call core.svec :a :b :c)
5   (call core.svec)
6   (call core._structtype TestMod :X %₃ %₄ %₅ false 3)
7   (= slot₁/X %₆)
8   (call core._setsuper! %₆ core.Any)
9   (call core.isdefinedglobal TestMod :X false)
10  (gotoifnot %₉ label₁₄)
11  TestMod.X
12  (= slot₂/if_val (call core._equiv_typedef %₁₁ %₆))
13  (goto label₁₅)
14  (= slot₂/if_val false)
15  slot₂/if_val
16  (gotoifnot %₁₅ label₂₀)
17  TestMod.X
18  (= slot₃/if_val %₁₇)
19  (goto label₂₁)
20  (= slot₃/if_val false)
21  slot₃/if_val
22  (gotoifnot %₁₅ label₂₃)
23  TestMod.T
24  (call core.svec core.Any %₂₃ core.Any)
25  (call core._typebody! %₂₁ %₆ %₂₄)
26  (constdecl TestMod.X %₂₅)
27  (latestworld)
28  TestMod.T
29  (call core.=== core.Any %₂₈)
30  (gotoifnot %₂₉ label₃₂)
31  (goto label₄₁)
32  (latestworld)
33  TestMod.X
34  (call core.apply_type core.Type %₃₃)
35  (call core.svec %₃₄ core.Any core.Any core.Any)
36  (call core.svec)
37  SourceLocation::1:1
38  (call core.svec %₃₅ %₃₆ %₃₇)
39  --- method core.nothing %₃₈
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
40  (latestworld)
41  (latestworld)
42  TestMod.X
43  (call core.apply_type core.Type %₄₂)
44  TestMod.T
45  (call core.svec %₄₃ core.Any %₄₄ core.Any)
46  (call core.svec)
47  SourceLocation::1:1
48  (call core.svec %₄₅ %₄₆ %₄₇)
49  --- method core.nothing %₄₈
    slots: [slot₁/#self#(!read) slot₂/a slot₃/b slot₄/c]
    1   TestMod.X
    2   (new %₁ slot₂/a slot₃/b slot₄/c)
    3   (return %₂)
50  (latestworld)
51  (return core.nothing)

########################################
# Struct with supertype and type params
struct X{U, S <: V <: T} <: Z
end
#---------------------
1   (global TestMod.X)
2   (latestworld)
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
16  (call core.isdefinedglobal TestMod :X false)
17  (gotoifnot %₁₆ label₂₁)
18  TestMod.X
19  (= slot₅/if_val (call core._equiv_typedef %₁₈ %₁₂))
20  (goto label₂₂)
21  (= slot₅/if_val false)
22  slot₅/if_val
23  (gotoifnot %₂₂ label₂₇)
24  TestMod.X
25  (= slot₆/if_val %₂₄)
26  (goto label₂₈)
27  (= slot₆/if_val false)
28  slot₆/if_val
29  (gotoifnot %₂₂ label₄₀)
30  TestMod.X
31  (call top.getproperty %₃₀ :body)
32  (call top.getproperty %₃₁ :body)
33  (call top.getproperty %₃₂ :parameters)
34  (call top.indexed_iterate %₃₃ 1)
35  (= slot₂/U (call core.getfield %₃₄ 1))
36  (= slot₁/iterstate (call core.getfield %₃₄ 2))
37  slot₁/iterstate
38  (call top.indexed_iterate %₃₃ 2 %₃₇)
39  (= slot₃/V (call core.getfield %₃₈ 1))
40  (call core.svec)
41  (call core._typebody! %₂₈ %₁₂ %₄₀)
42  (constdecl TestMod.X %₄₁)
43  (latestworld)
44  (latestworld)
45  slot₂/U
46  slot₃/V
47  TestMod.X
48  slot₂/U
49  slot₃/V
50  (call core.apply_type %₄₇ %₄₈ %₄₉)
51  (call core.apply_type core.Type %₅₀)
52  (call core.UnionAll %₄₆ %₅₁)
53  (call core.UnionAll %₄₅ %₅₂)
54  (call core.svec %₅₃)
55  (call core.svec)
56  SourceLocation::1:1
57  (call core.svec %₅₄ %₅₅ %₅₆)
58  --- method core.nothing %₅₇
    slots: [slot₁/#ctor-self#]
    1   (new slot₁/#ctor-self#)
    2   (return %₁)
59  (latestworld)
60  (return core.nothing)

########################################
# Struct with const and atomic fields
struct X
    const a
    @atomic b
    const @atomic c
end
#---------------------
1   (global TestMod.X)
2   (latestworld)
3   (call core.svec)
4   (call core.svec :a :b :c)
5   (call core.svec 1 :const 2 :atomic 3 :atomic 3 :const)
6   (call core._structtype TestMod :X %₃ %₄ %₅ false 3)
7   (= slot₁/X %₆)
8   (call core._setsuper! %₆ core.Any)
9   (call core.isdefinedglobal TestMod :X false)
10  (gotoifnot %₉ label₁₄)
11  TestMod.X
12  (= slot₂/if_val (call core._equiv_typedef %₁₁ %₆))
13  (goto label₁₅)
14  (= slot₂/if_val false)
15  slot₂/if_val
16  (gotoifnot %₁₅ label₂₀)
17  TestMod.X
18  (= slot₃/if_val %₁₇)
19  (goto label₂₁)
20  (= slot₃/if_val false)
21  slot₃/if_val
22  (gotoifnot %₁₅ label₂₃)
23  (call core.svec core.Any core.Any core.Any)
24  (call core._typebody! %₂₁ %₆ %₂₃)
25  (constdecl TestMod.X %₂₄)
26  (latestworld)
27  (latestworld)
28  TestMod.X
29  (call core.apply_type core.Type %₂₈)
30  (call core.svec %₂₉ core.Any core.Any core.Any)
31  (call core.svec)
32  SourceLocation::1:1
33  (call core.svec %₃₀ %₃₁ %₃₂)
34  --- method core.nothing %₃₃
    slots: [slot₁/#self#(!read) slot₂/a slot₃/b slot₄/c]
    1   TestMod.X
    2   (new %₁ slot₂/a slot₃/b slot₄/c)
    3   (return %₂)
35  (latestworld)
36  (return core.nothing)

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
2   (latestworld)
3   (call core.svec)
4   (call core.svec :a :b)
5   (call core.svec)
6   (call core._structtype TestMod :X %₃ %₄ %₅ false 2)
7   (= slot₁/X %₆)
8   (call core._setsuper! %₆ core.Any)
9   (call core.isdefinedglobal TestMod :X false)
10  (gotoifnot %₉ label₁₄)
11  TestMod.X
12  (= slot₂/if_val (call core._equiv_typedef %₁₁ %₆))
13  (goto label₁₅)
14  (= slot₂/if_val false)
15  slot₂/if_val
16  (gotoifnot %₁₅ label₂₀)
17  TestMod.X
18  (= slot₃/if_val %₁₇)
19  (goto label₂₁)
20  (= slot₃/if_val false)
21  slot₃/if_val
22  (gotoifnot %₁₅ label₂₃)
23  (call core.svec core.Any core.Any)
24  (call core._typebody! %₂₁ %₆ %₂₃)
25  (constdecl TestMod.X %₂₄)
26  (latestworld)
27  (latestworld)
28  TestMod.X
29  (call core.apply_type core.Type %₂₈)
30  (call core.svec %₂₉ core.Any core.Any)
31  (call core.svec)
32  SourceLocation::4:1
33  (call core.svec %₃₀ %₃₁ %₃₂)
34  --- method core.nothing %₃₃
    slots: [slot₁/#self#(!read) slot₂/a slot₃/b]
    1   TestMod.X
    2   (new %₁ slot₂/a slot₃/b)
    3   (return %₂)
35  (latestworld)
36  JuliaLowering.bind_docs!
37  (call core.tuple :field_docs)
38  (call core.apply_type core.NamedTuple %₃₇)
39  (call core.svec 1 "field a docs" 2 "field b docs")
40  (call core.tuple %₃₉)
41  (call %₃₈ %₄₀)
42  TestMod.X
43  SourceLocation::4:1
44  (call core.kwcall %₄₁ %₃₆ %₄₂ "X docs\n" %₄₃)
45  (return core.nothing)

########################################
# Struct with outer constructor
struct X{U}
    x::U
end
#---------------------
1   (global TestMod.X)
2   (latestworld)
3   (= slot₁/U (call core.TypeVar :U))
4   slot₁/U
5   (call core.svec %₄)
6   (call core.svec :x)
7   (call core.svec)
8   (call core._structtype TestMod :X %₅ %₆ %₇ false 1)
9   (= slot₂/X %₈)
10  (call core._setsuper! %₈ core.Any)
11  (call core.isdefinedglobal TestMod :X false)
12  (gotoifnot %₁₁ label₁₆)
13  TestMod.X
14  (= slot₃/if_val (call core._equiv_typedef %₁₃ %₈))
15  (goto label₁₇)
16  (= slot₃/if_val false)
17  slot₃/if_val
18  (gotoifnot %₁₇ label₂₂)
19  TestMod.X
20  (= slot₄/if_val %₁₉)
21  (goto label₂₃)
22  (= slot₄/if_val false)
23  slot₄/if_val
24  (gotoifnot %₁₇ label₃₀)
25  TestMod.X
26  (call top.getproperty %₂₅ :body)
27  (call top.getproperty %₂₆ :parameters)
28  (call top.indexed_iterate %₂₇ 1)
29  (= slot₁/U (call core.getfield %₂₈ 1))
30  slot₁/U
31  (call core.svec %₃₀)
32  (call core._typebody! %₂₃ %₈ %₃₁)
33  (constdecl TestMod.X %₃₂)
34  (latestworld)
35  (latestworld)
36  slot₁/U
37  TestMod.X
38  slot₁/U
39  (call core.apply_type %₃₇ %₃₈)
40  (call core.apply_type core.Type %₃₉)
41  (call core.UnionAll %₃₆ %₄₀)
42  (call core.svec %₄₁ core.Any)
43  (call core.svec)
44  SourceLocation::1:1
45  (call core.svec %₄₂ %₄₃ %₄₄)
46  --- method core.nothing %₄₅
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
47  (latestworld)
48  (latestworld)
49  TestMod.X
50  (call core.apply_type core.Type %₄₉)
51  slot₁/U
52  (call core.svec %₅₀ %₅₁)
53  slot₁/U
54  (call core.svec %₅₃)
55  SourceLocation::1:1
56  (call core.svec %₅₂ %₅₄ %₅₅)
57  --- method core.nothing %₅₆
    slots: [slot₁/#self#(!read) slot₂/x]
    1   TestMod.X
    2   (call core.apply_type %₁ static_parameter₁)
    3   (new %₂ slot₂/x)
    4   (return %₃)
58  (latestworld)
59  (return core.nothing)

########################################
# Struct with outer constructor where one typevar is constrained by the other
# See https://github.com/JuliaLang/julia/issues/27269)
struct X{T, S <: Vector{T}}
    v::Vector{S}
end
#---------------------
1   (global TestMod.X)
2   (latestworld)
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
16  (call core.isdefinedglobal TestMod :X false)
17  (gotoifnot %₁₆ label₂₁)
18  TestMod.X
19  (= slot₅/if_val (call core._equiv_typedef %₁₈ %₁₃))
20  (goto label₂₂)
21  (= slot₅/if_val false)
22  slot₅/if_val
23  (gotoifnot %₂₂ label₂₇)
24  TestMod.X
25  (= slot₆/if_val %₂₄)
26  (goto label₂₈)
27  (= slot₆/if_val false)
28  slot₆/if_val
29  (gotoifnot %₂₂ label₄₀)
30  TestMod.X
31  (call top.getproperty %₃₀ :body)
32  (call top.getproperty %₃₁ :body)
33  (call top.getproperty %₃₂ :parameters)
34  (call top.indexed_iterate %₃₃ 1)
35  (= slot₃/T (call core.getfield %₃₄ 1))
36  (= slot₁/iterstate (call core.getfield %₃₄ 2))
37  slot₁/iterstate
38  (call top.indexed_iterate %₃₃ 2 %₃₇)
39  (= slot₂/S (call core.getfield %₃₈ 1))
40  TestMod.Vector
41  slot₂/S
42  (call core.apply_type %₄₀ %₄₁)
43  (call core.svec %₄₂)
44  (call core._typebody! %₂₈ %₁₃ %₄₃)
45  (constdecl TestMod.X %₄₄)
46  (latestworld)
47  (latestworld)
48  slot₃/T
49  slot₂/S
50  TestMod.X
51  slot₃/T
52  slot₂/S
53  (call core.apply_type %₅₀ %₅₁ %₅₂)
54  (call core.apply_type core.Type %₅₃)
55  (call core.UnionAll %₄₉ %₅₄)
56  (call core.UnionAll %₄₈ %₅₅)
57  (call core.svec %₅₆ core.Any)
58  (call core.svec)
59  SourceLocation::1:1
60  (call core.svec %₅₇ %₅₈ %₅₉)
61  --- method core.nothing %₆₀
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
62  (latestworld)
63  (latestworld)
64  TestMod.X
65  (call core.apply_type core.Type %₆₄)
66  TestMod.Vector
67  slot₂/S
68  (call core.apply_type %₆₆ %₆₇)
69  (call core.svec %₆₅ %₆₈)
70  slot₃/T
71  slot₂/S
72  (call core.svec %₇₀ %₇₁)
73  SourceLocation::1:1
74  (call core.svec %₆₉ %₇₂ %₇₃)
75  --- method core.nothing %₇₄
    slots: [slot₁/#self#(!read) slot₂/v]
    1   TestMod.X
    2   (call core.apply_type %₁ static_parameter₁ static_parameter₂)
    3   (new %₂ slot₂/v)
    4   (return %₃)
76  (latestworld)
77  (return core.nothing)

########################################
# User defined inner constructors and helper functions for structs without type params
struct X
    x
    f() = new(1)
    X() = f() # this X() captures `f` (in flisp, as a Box :-/ )
    X(x) = new(x)
    X(y,z)::ReallyXIPromise = new(y+z)
    """
    Docs for X constructor
    """
    X(a,b,c) = new(a)
end
#---------------------
1   (= slot₂/f (call core.Box))
2   (global TestMod.X)
3   (latestworld)
4   (call core.svec)
5   (call core.svec :x)
6   (call core.svec)
7   (call core._structtype TestMod :X %₄ %₅ %₆ false 1)
8   (= slot₁/X %₇)
9   (call core._setsuper! %₇ core.Any)
10  (call core.isdefinedglobal TestMod :X false)
11  (gotoifnot %₁₀ label₁₅)
12  TestMod.X
13  (= slot₄/if_val (call core._equiv_typedef %₁₂ %₇))
14  (goto label₁₆)
15  (= slot₄/if_val false)
16  slot₄/if_val
17  (gotoifnot %₁₆ label₂₁)
18  TestMod.X
19  (= slot₅/if_val %₁₈)
20  (goto label₂₂)
21  (= slot₅/if_val false)
22  slot₅/if_val
23  (gotoifnot %₁₆ label₂₄)
24  (call core.svec core.Any)
25  (call core._typebody! %₂₂ %₇ %₂₄)
26  (constdecl TestMod.X %₂₅)
27  (latestworld)
28  (call core.svec)
29  (call core.svec)
30  (call JuliaLowering.eval_closure_type TestMod :#f##0 %₂₈ %₂₉)
31  (latestworld)
32  TestMod.#f##0
33  (new %₃₂)
34  slot₂/f
35  (call core.setfield! %₃₄ :contents %₃₃)
36  (latestworld)
37  TestMod.#f##0
38  (call core.svec %₃₇)
39  (call core.svec)
40  SourceLocation::3:5
41  (call core.svec %₃₈ %₃₉ %₄₀)
42  --- method core.nothing %₄₁
    slots: [slot₁/#self#(!read)]
    1   TestMod.X
    2   (new %₁ 1)
    3   (return %₂)
43  (latestworld)
44  (latestworld)
45  TestMod.X
46  (call core.apply_type core.Type %₄₅)
47  (call core.svec %₄₆)
48  (call core.svec)
49  SourceLocation::4:5
50  (call core.svec %₄₇ %₄₈ %₄₉)
51  --- code_info
    slots: [slot₁/#ctor-self#(!read) slot₂/f(!read)]
    1   (captured_local 1)
    2   (call core.isdefined %₁ :contents)
    3   (gotoifnot %₂ label₅)
    4   (goto label₇)
    5   (newvar slot₂/f)
    6   slot₂/f
    7   (call core.getfield %₁ :contents)
    8   (call %₇)
    9   (return %₈)
52  slot₂/f
53  (call core.svec %₅₂)
54  (call JuliaLowering.replace_captured_locals! %₅₁ %₅₃)
55  --- method core.nothing %₅₀ %₅₄
56  (latestworld)
57  (latestworld)
58  TestMod.X
59  (call core.apply_type core.Type %₅₈)
60  (call core.svec %₅₉ core.Any)
61  (call core.svec)
62  SourceLocation::5:5
63  (call core.svec %₆₀ %₆₁ %₆₂)
64  --- method core.nothing %₆₃
    slots: [slot₁/#ctor-self# slot₂/x]
    1   slot₁/#ctor-self#
    2   (new %₁ slot₂/x)
    3   (return %₂)
65  (latestworld)
66  (latestworld)
67  TestMod.X
68  (call core.apply_type core.Type %₆₇)
69  (call core.svec %₆₈ core.Any core.Any)
70  (call core.svec)
71  SourceLocation::6:5
72  (call core.svec %₆₉ %₇₀ %₇₁)
73  --- method core.nothing %₇₂
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
74  (latestworld)
75  (latestworld)
76  TestMod.X
77  (call core.apply_type core.Type %₇₆)
78  (call core.svec %₇₇ core.Any core.Any core.Any)
79  (call core.svec)
80  SourceLocation::10:5
81  (call core.svec %₇₈ %₇₉ %₈₀)
82  --- method core.nothing %₈₁
    slots: [slot₁/#ctor-self# slot₂/a slot₃/b(!read) slot₄/c(!read)]
    1   slot₁/#ctor-self#
    2   (new %₁ slot₂/a)
    3   (return %₂)
83  (latestworld)
84  TestMod.X
85  (call core.apply_type core.Type %₈₄)
86  (call JuliaLowering.bind_docs! %₈₅ "Docs for X constructor\n" %₈₁)
87  (return core.nothing)

########################################
# User defined inner constructors and helper functions for structs with type params
struct X{S,T}
    x
    X{A,B}() = new(1)
    X{U,V}() where {U,V} = new(1)
    f() = new{A,B}(1)
end
#---------------------
1   (newvar slot₅/f)
2   (global TestMod.X)
3   (latestworld)
4   (= slot₂/S (call core.TypeVar :S))
5   (= slot₃/T (call core.TypeVar :T))
6   slot₂/S
7   slot₃/T
8   (call core.svec %₆ %₇)
9   (call core.svec :x)
10  (call core.svec)
11  (call core._structtype TestMod :X %₈ %₉ %₁₀ false 1)
12  (= slot₄/X %₁₁)
13  (call core._setsuper! %₁₁ core.Any)
14  (call core.isdefinedglobal TestMod :X false)
15  (gotoifnot %₁₄ label₁₉)
16  TestMod.X
17  (= slot₈/if_val (call core._equiv_typedef %₁₆ %₁₁))
18  (goto label₂₀)
19  (= slot₈/if_val false)
20  slot₈/if_val
21  (gotoifnot %₂₀ label₂₅)
22  TestMod.X
23  (= slot₉/if_val %₂₂)
24  (goto label₂₆)
25  (= slot₉/if_val false)
26  slot₉/if_val
27  (gotoifnot %₂₀ label₃₈)
28  TestMod.X
29  (call top.getproperty %₂₈ :body)
30  (call top.getproperty %₂₉ :body)
31  (call top.getproperty %₃₀ :parameters)
32  (call top.indexed_iterate %₃₁ 1)
33  (= slot₂/S (call core.getfield %₃₂ 1))
34  (= slot₁/iterstate (call core.getfield %₃₂ 2))
35  slot₁/iterstate
36  (call top.indexed_iterate %₃₁ 2 %₃₅)
37  (= slot₃/T (call core.getfield %₃₆ 1))
38  (call core.svec core.Any)
39  (call core._typebody! %₂₆ %₁₁ %₃₈)
40  (constdecl TestMod.X %₃₉)
41  (latestworld)
42  (latestworld)
43  TestMod.X
44  TestMod.A
45  TestMod.B
46  (call core.apply_type %₄₃ %₄₄ %₄₅)
47  (call core.apply_type core.Type %₄₆)
48  (call core.svec %₄₇)
49  (call core.svec)
50  SourceLocation::3:5
51  (call core.svec %₄₈ %₄₉ %₅₀)
52  --- method core.nothing %₅₁
    slots: [slot₁/#ctor-self#]
    1   slot₁/#ctor-self#
    2   (new %₁ 1)
    3   (return %₂)
53  (latestworld)
54  (latestworld)
55  (= slot₆/U (call core.TypeVar :U))
56  (= slot₇/V (call core.TypeVar :V))
57  TestMod.X
58  slot₆/U
59  slot₇/V
60  (call core.apply_type %₅₇ %₅₈ %₅₉)
61  (call core.apply_type core.Type %₆₀)
62  (call core.svec %₆₁)
63  slot₆/U
64  slot₇/V
65  (call core.svec %₆₃ %₆₄)
66  SourceLocation::4:5
67  (call core.svec %₆₂ %₆₅ %₆₆)
68  --- method core.nothing %₆₇
    slots: [slot₁/#ctor-self#]
    1   slot₁/#ctor-self#
    2   (new %₁ 1)
    3   (return %₂)
69  (latestworld)
70  (call core.svec)
71  (call core.svec)
72  (call JuliaLowering.eval_closure_type TestMod :#f##1 %₇₀ %₇₁)
73  (latestworld)
74  TestMod.#f##1
75  (new %₇₄)
76  (= slot₅/f %₇₅)
77  (latestworld)
78  TestMod.#f##1
79  (call core.svec %₇₈)
80  (call core.svec)
81  SourceLocation::5:5
82  (call core.svec %₇₉ %₈₀ %₈₁)
83  --- method core.nothing %₈₂
    slots: [slot₁/#self#(!read)]
    1   TestMod.X
    2   TestMod.A
    3   TestMod.B
    4   (call core.apply_type %₁ %₂ %₃)
    5   (new %₄ 1)
    6   (return %₅)
84  (latestworld)
85  (return core.nothing)

########################################
# new() calls with splats; `Any` fields
struct X
    x
    y
    X(xs) = new(xs...)
end
#---------------------
1   (global TestMod.X)
2   (latestworld)
3   (call core.svec)
4   (call core.svec :x :y)
5   (call core.svec)
6   (call core._structtype TestMod :X %₃ %₄ %₅ false 2)
7   (= slot₁/X %₆)
8   (call core._setsuper! %₆ core.Any)
9   (call core.isdefinedglobal TestMod :X false)
10  (gotoifnot %₉ label₁₄)
11  TestMod.X
12  (= slot₂/if_val (call core._equiv_typedef %₁₁ %₆))
13  (goto label₁₅)
14  (= slot₂/if_val false)
15  slot₂/if_val
16  (gotoifnot %₁₅ label₂₀)
17  TestMod.X
18  (= slot₃/if_val %₁₇)
19  (goto label₂₁)
20  (= slot₃/if_val false)
21  slot₃/if_val
22  (gotoifnot %₁₅ label₂₃)
23  (call core.svec core.Any core.Any)
24  (call core._typebody! %₂₁ %₆ %₂₃)
25  (constdecl TestMod.X %₂₄)
26  (latestworld)
27  (latestworld)
28  TestMod.X
29  (call core.apply_type core.Type %₂₈)
30  (call core.svec %₂₉ core.Any)
31  (call core.svec)
32  SourceLocation::4:5
33  (call core.svec %₃₀ %₃₁ %₃₂)
34  --- method core.nothing %₃₃
    slots: [slot₁/#ctor-self# slot₂/xs]
    1   slot₁/#ctor-self#
    2   (call core._apply_iterate top.iterate core.tuple slot₂/xs)
    3   (splatnew %₁ %₂)
    4   (return %₃)
35  (latestworld)
36  (return core.nothing)

########################################
# new() calls with splats; typed fields
struct X{T}
    x::T
    y::A
    X{T}(xs) where {T} = new(xs...)
end
#---------------------
1   (global TestMod.X)
2   (latestworld)
3   (= slot₁/T (call core.TypeVar :T))
4   slot₁/T
5   (call core.svec %₄)
6   (call core.svec :x :y)
7   (call core.svec)
8   (call core._structtype TestMod :X %₅ %₆ %₇ false 2)
9   (= slot₂/X %₈)
10  (call core._setsuper! %₈ core.Any)
11  (call core.isdefinedglobal TestMod :X false)
12  (gotoifnot %₁₁ label₁₆)
13  TestMod.X
14  (= slot₄/if_val (call core._equiv_typedef %₁₃ %₈))
15  (goto label₁₇)
16  (= slot₄/if_val false)
17  slot₄/if_val
18  (gotoifnot %₁₇ label₂₂)
19  TestMod.X
20  (= slot₅/if_val %₁₉)
21  (goto label₂₃)
22  (= slot₅/if_val false)
23  slot₅/if_val
24  (gotoifnot %₁₇ label₃₀)
25  TestMod.X
26  (call top.getproperty %₂₅ :body)
27  (call top.getproperty %₂₆ :parameters)
28  (call top.indexed_iterate %₂₇ 1)
29  (= slot₁/T (call core.getfield %₂₈ 1))
30  slot₁/T
31  TestMod.A
32  (call core.svec %₃₀ %₃₁)
33  (call core._typebody! %₂₃ %₈ %₃₂)
34  (constdecl TestMod.X %₃₃)
35  (latestworld)
36  (latestworld)
37  (= slot₃/T (call core.TypeVar :T))
38  TestMod.X
39  slot₃/T
40  (call core.apply_type %₃₈ %₃₉)
41  (call core.apply_type core.Type %₄₀)
42  (call core.svec %₄₁ core.Any)
43  slot₃/T
44  (call core.svec %₄₃)
45  SourceLocation::4:5
46  (call core.svec %₄₂ %₄₄ %₄₅)
47  --- method core.nothing %₄₆
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
48  (latestworld)
49  (return core.nothing)

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

