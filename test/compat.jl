using Test
using JuliaLowering
const JS = JuliaSyntax
const JL = JuliaLowering

# Parse string->expr->tree->expr.  This is for bulk testing that the expr->tree
# conversion preserves semantics.
function parse_ete(args...)
    outex, pos = JS.core_parser_hook(args...)
    st = JL.expr_to_syntaxtree(outex)
    local out
    try
        out = Expr(st)
    catch e
        show(args[1])
        @error "Failed to convert back to expr:" st
        Base.showerror(stdout, e, Base.catch_backtrace())
        return outex, pos
    end
    return out, pos
    # @warn "after:" st
end

function fix_module(m::Module)
    # Make `m` equivalent to `module anonymous end`
    Core.eval(m, :(eval(x) = Core.eval($m, x)))
    Core.eval(m, :(include(x) = Base.include($m, x)))
    m
end

test_mod_1 = fix_module(Module())
test_mod_2 = fix_module(Module())

# parse and eval "normally" vs. with expr->tree->expr transformation, returning
# the result of both evaluations.
function test_eval_ete(s::AbstractString)
    ps = JS.ParseStream(s)
    JS.parse!(ps)
    good_tree = JS.build_tree(JL.SyntaxTree, ps)
    local good_expr
    try
        good_expr = Expr(good_tree)
        try
            good_out = Core.eval(test_mod_1, good_expr)
            Core._setparser!(parse_ete)
            test_out = Core.eval(test_mod_2, Meta.parseall(s))
            # @warn "reference tree:"
            # show(stdout, MIME("text/plain"), good_tree)
            @test good_out == test_out
        catch e
            show(stdout, MIME("text/plain"), good_expr)
            Base.showerror(stdout, e, Base.catch_backtrace())
            @test "test threw; see output" == ""
        finally
            Core._setparser!(JS.core_parser_hook)
            # Core.eval(test_mod_2, good_expr) # even them out?
        end

    catch e_
        @error good_tree
        Base.showerror(stdout, e_, Base.catch_backtrace())
        @test "failed to convert known-good syntax tree???" == ""
    end
end

# Remove any information that can't be recovered from an Expr
function normalize_st!(st)
    k = JS.kind(st)

    if JS.is_infix_op_call(st) && (k === K"call" || k === K"dotcall")
        # Infix calls are not preserved in Expr
        args = JS.children(st)

        pre_st_args = JL.NodeId[args[2]._id, args[1]._id]
        for c in args[3:end]
            # there has got to be a better way
            push!(pre_st_args, c._id)
        end
        pre_st_flags = (JS.flags(st) & ~JS.INFIX_FLAG) | JS.PREFIX_CALL_FLAG
        pre_st = JL.makeleaf(st._graph, st, k)
        JL.setchildren!(pre_st._graph, pre_st._id, pre_st_args)
        JL.setflags!(pre_st._graph, pre_st._id, pre_st_flags)
        return pre_st
    elseif k in JS.KSet"tuple block macrocall"
        # Parens are not preserved
        JL.setflags!(st._graph, st._id, JS.flags(st) & ~JS.PARENS_FLAG)
    elseif k === K"toplevel"
        JL.setflags!(st._graph, st._id, JS.flags(st) & ~JS.TOPLEVEL_SEMICOLONS_FLAG)
    end

    # All ops are prefix ops in an expr
    JL.setflags!(st._graph, st._id, JS.flags(st) & ~JS.PREFIX_OP_FLAG)

    return st
end

function st_roughly_equal(st_good, st_test)
    st_good = normalize_st!(st_good)
    out = kind(st_good) === kind(st_test) &&
        JS.flags(st_good) === JS.flags(st_test) &&
        JS.numchildren(st_good) === JS.numchildren(st_test) &&
        JS.is_leaf(st_good) === JS.is_leaf(st_test) &&
        get(st_good, :value, nothing) === get(st_test, :value, nothing) &&
        get(st_good, :name_val, nothing) === get(st_test, :name_val, nothing) &&
        all(map(st_roughly_equal, JS.children(st_good), JS.children(st_test)))
    !out && @warn("!st_roughly_equal (normalized_reference, test):",
                  JS.sourcetext(st_good), st_good, st_test)
    return out
end
# @test tree ~= tree->expr->tree
function tet_eq(s::String)
    p1 = JS.parsestmt(SyntaxTree, s; ignore_errors=true)
    p2 = JL.expr_to_syntaxtree(Expr(p1))
    @test st_roughly_equal(p1, p2)
end

@testset "expr->syntaxtree" begin
    @testset "semantics only" begin
        test_eval_ete("let x = 2; x += 5; x -= 1; [1] .*= 1; end")
        test_eval_ete("try; 1; catch e; e; else; 2; finally; 3; end")
        test_eval_ete("for x in 1:2, y in 3:4; x + y; end")

        test_eval_ete("[x+y for x in 1:2, y in 3:4]")
        test_eval_ete("Int[x+y for x in 1:2, y in 3:4 if true]")

        test_eval_ete("for x in 1; x+=1\n if true\n continue \n elseif false \n break\n end\n end")
        test_eval_ete("@time 1")
        test_eval_ete("Base.Meta.@lower 1")
        test_eval_ete("function foo(x, y=1; z, what::Int=5); x + y + z + what; end; foo(1,2;z=3)")

        test_eval_ete("(()->1)()")
        test_eval_ete("((x)->2)(3)")
        test_eval_ete("((x,y)->4)(5,6)")
        test_eval_ete("filter([1,2,3]) do x; x > 1; end")
        test_eval_ete("""
        struct X
            f1::Int # hi
            "foo"
            f2::Int
            f3::Int
            X(y) = new(y,y,y)
        end
        """)
        test_eval_ete("global x,y")
        test_eval_ete("global (x,y)")
        test_eval_ete("999999999999999999999999999999999999999")
    end

    @testset "syntaxtree equivalence (tests from JuliaSyntax expr.jl)" begin
        tet_eq("begin a\nb\n\nc\nend")
        tet_eq("(a;b;c)")
        tet_eq("begin end")
        tet_eq("(;;)")
        tet_eq("a;b")
        tet_eq("module A\n\nbody\nend")
        tet_eq("function f()\na\n\nb\nend")
        tet_eq("f() = 1")
        tet_eq("macro f()\na\nend")
        tet_eq("function f end")
        tet_eq("macro f end")
        tet_eq("function (f() where T) end")
        tet_eq("function (f()::S) end")
        tet_eq("a -> b")
        tet_eq("(a,) -> b")
        tet_eq("(a where T) -> b")
        tet_eq("a -> (\nb;c)")
        tet_eq("a -> begin\nb\nc\nend")
        tet_eq("(a;b=1) -> c")
        tet_eq("(a...;b...) -> c")
        tet_eq("(;) -> c")
        tet_eq("a::T -> b")
        tet_eq("if a\nb\nelseif c\n d\nend")
        tet_eq("let i=is, j=js\nbody\nend")
        tet_eq("for x=xs\n\nend")
        tet_eq("for x=xs\ny\nend")
        tet_eq("while cond\n\nend")
        tet_eq("while cond\ny\nend")
        tet_eq("f() = xs")
        tet_eq("f() =\n(a;b)")
        tet_eq("f() =\nbegin\na\nb\nend")
        tet_eq("let f(x) =\ng(x)=1\nend")
        tet_eq("f() .= xs")
        tet_eq("for i=is body end")
        tet_eq("for i=is, j=js\nbody\nend")
        tet_eq("function (xs...)\nbody end")
        tet_eq("\"str\"")
        tet_eq("\"\$(\"str\")\"")
        tet_eq("```\n  a\n  b```")
        tet_eq("\"\"\"\n  a\n  \$x\n  b\n  c\"\"\"")
        tet_eq("`x")
        tet_eq("`")
        tet_eq("'a'")
        tet_eq("'α'")
        tet_eq("'\\xce\\xb1'")
        tet_eq("f(x) do y\n body end")
        tet_eq("@f(x) do y body end")
        tet_eq("f(x; a=1) do y body end")
        tet_eq("g(f(x) do y\n body end)")
        tet_eq("f(a=1)")
        tet_eq("f(; b=2)")
        tet_eq("f(a=1; b=2)")
        tet_eq("f(a; b; c)")
        tet_eq("+(a=1,)")
        tet_eq("(a=1)()")
        tet_eq("(x=1) != 2")
        tet_eq("+(a=1)")
        tet_eq("(a=1)'")
        tet_eq("(a=1)'ᵀ")
        tet_eq("f.(a=1; b=2)")
        tet_eq("(a=1,)")
        tet_eq("(a=1,; b=2)")
        tet_eq("(a=1,; b=2; c=3)")
        tet_eq("x[i=j]")
        tet_eq("(i=j)[x]")
        tet_eq("x[a, b; i=j]")
        tet_eq("(i=j){x}")
        tet_eq("x{a, b; i=j}")
        tet_eq("[a=1,; b=2]")
        tet_eq("{a=1,; b=2}")
        tet_eq("f(a .= 1)")
        tet_eq("f(((a = 1)))")
        tet_eq("(((a = 1)),)")
        tet_eq("(;((a = 1)),)")
        tet_eq("a.b")
        tet_eq("a.\$b")
        tet_eq("a.:b")
        tet_eq("a.@b x")
        tet_eq("f.(x,y)")
        tet_eq("f.(x=1)")
        tet_eq("f.(a=1; b=2)")
        tet_eq("(a=1).()")
        tet_eq("x .+ y")
        tet_eq("(x=1) .+ y")
        tet_eq("a .< b .< c")
        tet_eq("a .< (.<) .< c")
        tet_eq(".*(x)")
        tet_eq(".+(x)")
        tet_eq(".+x")
        tet_eq("(.+)(x)")
        tet_eq("(.+).(x)")
        tet_eq(".+")
        tet_eq(":.+")
        tet_eq(":(.+)")
        tet_eq("quote .+ end")
        tet_eq(".+{x}")
        tet_eq(":.=")
        tet_eq(":(.=)")
        tet_eq("f(.+)")
        tet_eq("(a, .+)")
        tet_eq("A.:.+")
        tet_eq("./x")
        tet_eq("x += y")
        tet_eq("x .+= y")
        tet_eq(":+=")
        tet_eq(":(+=)")
        tet_eq(":.+=")
        tet_eq(":(.+=)")
        tet_eq("x \u2212= y")
        tet_eq("let x=1\n end")
        tet_eq("let x=1 ; end")
        tet_eq("let x ; end")
        tet_eq("let x::1 ; end")
        tet_eq("let x=1,y=2 end")
        tet_eq("let x+=1 ; end")
        tet_eq("let ; end")
        tet_eq("let ; body end")
        tet_eq("let\na\nb\nend")
        tet_eq("A where T")
        tet_eq("A where {T}")
        tet_eq("A where {S, T}")
        tet_eq("A where {X, Y; Z}")
        tet_eq("@m\n")
        tet_eq("\n@m")
        tet_eq("@m(x; a)")
        tet_eq("@m(a=1; b=2)")
        tet_eq("@.")
        tet_eq("using A: @.")
        tet_eq("@var\"#\" a")
        tet_eq("A.@var\"#\" a")
        tet_eq("@S[a,b]")
        tet_eq("@S[a b]")
        tet_eq("@S[a; b]")
        tet_eq("@S[a ;; b]")
        tet_eq("var\"x\"")
        tet_eq("var\"\"")
        tet_eq("var\"\\\"\"")
        tet_eq("var\"\\\\\\\"\"")
        tet_eq("var\"\\\\x\"")
        tet_eq("var\"x\"+y")
        tet_eq("[x,y ; z]")
        tet_eq("[a ;;; b ;;;; c]")
        tet_eq("[a b ; c d]")
        tet_eq("[a\nb]")
        tet_eq("[a b]")
        tet_eq("[a b ; c d]")
        tet_eq("T[a ;;; b ;;;; c]")
        tet_eq("T[a b ; c d]")
        tet_eq("T[a\nb]")
        tet_eq("T[a b]")
        tet_eq("T[a b ; c d]")
        tet_eq("(x for a in as for b in bs)")
        tet_eq("(x for a in as, b in bs)")
        tet_eq("(x for a in as, b in bs if z)")
        tet_eq("(x for a in as, b in bs for c in cs, d in ds)")
        tet_eq("(x for a in as for b in bs if z)")
        tet_eq("(x for a in as if z for b in bs)")
        tet_eq("[x for a = as for b = bs if cond1 for c = cs if cond2]" )
        tet_eq("[x for a = as if begin cond2 end]" )
        tet_eq("(x for a in as if z)")
        tet_eq("try x catch e; y end")
        tet_eq("try x finally y end")
        tet_eq("try x catch e; y finally z end")
        tet_eq("try x catch e; y else z end")
        tet_eq("try x catch e; y else z finally w end")
        tet_eq("try x finally y catch e z end")
        tet_eq("try x end")
        tet_eq("2x")
        tet_eq("(2)(3)x")
        tet_eq("\"x\" f")
        tet_eq("\n\"x\" f")
        tet_eq("foo\"str\"")
        tet_eq("\n`str`")
        tet_eq("foo`str`")
        tet_eq("foo`str`flag")
        tet_eq("foo```\n  a\n  b```")
        tet_eq("@foo_cmd `str`")
        tet_eq("return x")
        tet_eq("return")
        tet_eq("0x00000000000000001")
        tet_eq("(0x00000000000000001)")
        tet_eq("struct A end")
        tet_eq("mutable struct A end")
        tet_eq("struct A <: B \n a::X \n end")
        tet_eq("struct A \n a \n b \n end")
        tet_eq("struct A const a end")
        tet_eq("struct A \n \"doc\" \n a end")
        tet_eq("export a")
        tet_eq("export @a")
        tet_eq("export @var\"'\"")
        tet_eq("export a, \n @b")
        tet_eq("export +, ==")
        tet_eq("export \n a")
        tet_eq("global x")
        tet_eq("local x")
        tet_eq("global x,y")
        tet_eq("global const x = 1")
        tet_eq("local const x = 1")
        tet_eq("const global x = 1")
        tet_eq("const local x = 1")
        tet_eq("const x,y = 1,2")
        tet_eq("const x = 1")
        tet_eq("global x ~ 1")
        tet_eq("global x += 1")
        tet_eq("global (x,y)")
        tet_eq("local (x,y)")
        tet_eq("(;)")
        tet_eq("(; a=1)")
        tet_eq("(; a=1; b=2)")
        tet_eq("(a; b; c,d)")
        tet_eq("module A end")
        tet_eq("baremodule A end")
        tet_eq("--")
        tet_eq("(x")
        tet_eq("x do")
        tet_eq("x var\"y\"")
        tet_eq("var\"y")
        tet_eq("import A")
        tet_eq("import A.(:b).:c: x.:z")
        tet_eq("import A.:+")
        tet_eq("import A.(:+)")
        tet_eq("import A.:(+)")
    end
end
