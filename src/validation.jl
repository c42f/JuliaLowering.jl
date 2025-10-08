struct ValidationDiagnostic <: Exception
    sts::SyntaxList
    msg::String
end
ValidationDiagnostic(st::SyntaxTree, msg::String) =
    ValidationDiagnostic(SyntaxList(syntax_graph(st), NodeId[st._id]), msg)

# This could probably be one or several scoped values instead.
"""
Error vector (shared per invocation of valid_st1) and flags.

Flags are mainly to avoid keyword argument spam for parameters that are updated
rarely, but apply recursively, usually to remember the kinds of structures we're
in (e.g. vcx.toplevel becomes false in any function).

By default, assume we are validating a usual lowering input (top-level) that has
been macroexpanded.
"""
struct Validation1Context
    _flags::Base.PersistentDict{Symbol, Any}
    errors::Vector{ValidationDiagnostic}
    # warnings::Vector{ValidationDiagnostic}
end
Validation1Context() = Validation1Context(
    Base.PersistentDict{Symbol, Any}(
        :speculative => false, # match not required; disable errors and return a bool
        :toplevel => true, # not in any lambda body
        :in_gscope => true, # not in any scope; implies toplevel
        :in_loop => false, # break/continue allowed
        :inner_cond => false, # inner methods not allowed.  true in ? (args 2-3), &&, and ||
        :return_ok => true, # yes usually (even outside of functions), no in comprehensions/generators
        # syntax TODO: no return in finally? type declarations?

        # We currently always parse to K"=", but Expr(:kw) is valid here and Expr(:(=)) is not
        # :assign_ok => true, # no in vect, curly, [typed_]h/v/ncat
        # :beginend_ok => false # once this is different from the identifier

        # vst0 shares this context type since macro expansion doesn't recurse
        # into some forms, and most parts of the AST are the same.
        :unexpanded => false,
        :quote_level => 0,
    ), ValidationDiagnostic[])

with(vcx::Validation1Context, p1, pairs...) =
    Validation1Context(Base.PersistentDict{Symbol, Any}(vcx._flags, p1), vcx.errors)
with(vcx::Validation1Context, p1, p2, pairs...) = with(with(vcx, p1), p2, pairs...)

function Base.getproperty(vcx::Validation1Context, param::Symbol)
    param in (:errors, :warnings, :_flags) ?
        getfield(vcx, param) :
        get(getfield(vcx, :_flags), param, nothing)
end

"""
Executable grammar of the input language to lowering (post-macro-expansion).

This should serve three purposes:
(1) A readable reference for the julia AST structure.
(2) A set of assumptions we can use in lowering (a guard against many forms of
    invalid input).  If `valid_st1(st)` returns true, lowering is expected to
    produce correct output given `st` (possibly by throwing a LoweringError).
(3) The place we throw helpful user-facing errors given malformed ASTs.

Only AST structure is checked.  Roughly, this means "kinds and child counts in
context".  A tree `t` has valid structure if, given the kinds and child count of
all its ancestors, and the position within its parent of `t` and all its
ancestors, we know how to lower `t` to IR.

We don't check some other things:
- This pass assumes that required attributes exist, that leaf-only (or not)
  kinds are leaves (or not), and that syntax flags are valid per kind; these can
  be checked beforehand in a linear pass over the nodes.
- Scope issues are caught later in lowering, e.g. declaring something local and
  global.

"""
function valid_st1(st::SyntaxTree)
    vcx = Validation1Context()
    valid = valid_st1(vcx, st)
    for (i, e) in enumerate(vcx.errors)
        printstyled("error $i:\n"; color=:red)
        showerror(stdout, LoweringError(e.sts[1], e.msg))
        for st_ in e.sts[2:end]; show(st_); end
        printstyled("---------------------------------\n"; color=:red)
    end
    return valid
end

function valid_st1(vcx::Validation1Context, st::SyntaxTree)
    pass = vst1_stmt(vcx, st)
    !pass && isempty(vcx.errors) &&
        fail(vcx, st, "invalid syntax: unknown kind `$(kind(st))` or number of arguments ($(numchildren(st)))")
    return pass
end

# temp function to keep LoweringErrors the same as before, producing only one
# error with only one associated tree
function valid_st1_or_throw(st::SyntaxTree)
    vcx = Validation1Context()
    valid = valid_st1(vcx, st)
    if !isempty(vcx.errors) & !valid
        e1 = vcx.errors[1]
        throw(LoweringError(e1.sts[1], e1.msg))
    elseif isempty(vcx.errors) & valid
        return nothing
    else
        throw(LoweringError(st, "validator bug: returned $valid but with $(length(vcx.errors)) errors"))
    end
end

vst1_value(vcx::Validation1Context, st::SyntaxTree; need_value=true) = @stm st begin
    (leaf, when=kind(leaf) in KSet"""Identifier Value Symbol Integer Float
        String Char Bool CmdString HexInt OctInt BinInt""") -> true

    # Container nodes that may or may not be values depending on their contents;
    # callers of vst1_value can specify that they don't need a value.  Most
    # other forms are always a value.
    [K"block" _...] -> vst1_block(vcx, st; need_value)
    [K"let" [K"block" decls...] body] -> allv(vst1_symdecl_or_assign, vcx, decls) &
        vst1_block(with(vcx, :in_gscope=>false), body; need_value)
    [K"if" cond t] -> vst1_value(vcx, cond) &
        vst1_value(vcx.toplevel ? vcx : with(vcx, :inner_cond=>true), t; need_value)
    [K"if" cond t f] -> vst1_value(vcx, cond) &
        vst1_value(vcx.toplevel ? vcx : with(vcx, :inner_cond=>true), t; need_value) &
        vst1_else(vcx.toplevel ? vcx : with(vcx, :inner_cond=>true), f; need_value)

    # op-assign will perform the op, but fail to assign with a bad lhs, so we
    # disallow it here
    [K"="    l r] -> vst1_assign_lhs(vcx, l) & vst1_value(vcx, r)
    [K"op="  l op r] -> vst1_assign_lhs(vcx, l) & vst1_ident(vcx, op) & vst1_value(vcx, r)
    [K".="   l r] -> vst1_dotassign_lhs(vcx, l) & vst1_value(vcx, r)
    [K".op=" l op r] -> vst1_dotassign_lhs(vcx, l) & vst1_ident(vcx, op) & vst1_value(vcx, r)

    [K"function" _...] -> !vcx.inner_cond || vcx.toplevel ? vst1_function(vcx, st) :
        fail(vcx, st, "conditional inner method definitions are not supported; use `()->()` syntax instead")
    [K"call" _...] -> vst1_call(vcx, st)
    [K"dotcall" _...] -> vst1_dotcall(vcx, st)
    [K"return"] -> vcx.return_ok || fail(vcx, st, "`return` not allowed inside comprehension or generator")
    [K"return" val] -> vcx.return_ok ? vst1_value(vcx, val) :
        fail(vcx, st, "`return` not allowed inside comprehension or generator")
    [K"continue"] -> vcx.in_loop || fail(vcx, st, "`continue` must be used inside a `while` or `for` loop")
    [K"break"] -> vcx.in_loop || fail(vcx, st, "`break` must be used inside a `while` or `for` loop")
    [K"?" cond t f] -> vst1_value(vcx, cond) &
        vst1_value(vcx.toplevel ? vcx : with(vcx, :inner_cond=>true), t) &
        vst1_value(vcx.toplevel ? vcx : with(vcx, :inner_cond=>true), f)
    [K"for" [K"iteration" is...] [K"block" body...]] ->
        allv(vst1_iter, vcx, is) &
        allv(vst1_stmt, with(vcx, :in_loop=>true, :in_gscope=>false), body)
    [K"while" cond [K"block" body...]] ->
        vst1_value(vcx, cond) &
        allv(vst1_stmt, with(vcx, :in_loop=>true, :in_gscope=>false), body)
    [K"try" _...] -> vst1_try(vcx, st)
    [K"macrocall" _...] -> vcx.unexpanded ? vst0_macrocall(vcx, st) :
        fail(vcx, st, "macrocall not valid in AST after macro expansion")
    [K"quote" x] -> vcx.unexpanded ? vst0_quoted(with(vcx, :quote_level=>1), x) :
        fail(vcx, st, "interpolating quote not valid in AST after macro expansion")
    [K"$" x] -> fail(vcx, st, raw"`$` expression outside string or quote")
    [K"tuple" xs... [K"parameters" kws...]] ->
        allv(vst1_splat_or_val, vcx, xs) & allv(vst1_call_arg, vcx, kws)
    [K"tuple" xs...] -> allv(vst1_splat_or_val, vcx, xs)
    [K"." x y] -> vst1_value(vcx, x) & vst1_dot_rhs(vcx, y)
    [K"." x] -> vst1_value(vcx, x)
    [K":"] -> true # ast TODO: this doesn't need to be a kind.  note a:b is a call, this is a[:] or just :
    [K"curly" t xs...] -> vst1_value(vcx, t) & allv(vst1_value_curly_typevar, vcx, xs)
    [K"where" lhs rhs] -> vst1_value(vcx, lhs) & vst1_where_rhs(vcx, rhs)
    [K"string" xs...] -> allv(vst1_value, vcx, xs)
    [K"->" _...] -> vst1_lam(vcx, st)
    [K"generator" _...] -> vst1_generator(vcx, st)
    [K"comprehension" g] -> vst1_generator(vcx, g)
    [K"typed_comprehension" t g] -> vst1_value(with(vcx, :return_ok=>false), t) & vst1_generator(vcx, g)
    [K"comparison" xs...] -> length(xs) < 3 || iseven(length(xs)) ?
        fail(vcx, st, "`comparison` expects n>=3 args and odd n") :
        # TODO: xs[2:2:end] should just be identifier or (. identifier)
        allv(vst1_value, vcx, xs[2:2:end]) & allv(vst1_value, vcx, xs[1:2:end])
    [K"doc" [K"string" strs...] x] -> allv(vst1_value, vcx, strs) & vst1_documented(vcx, x)
    [K"<:" x y] -> vst1_value(vcx, x) & vst1_value(vcx, y)
    [K">:" x y] -> vst1_value(vcx, x) & vst1_value(vcx, y)
    [K"-->" x y] -> vst1_value(vcx, x) & vst1_value(vcx, y)
    [K"::" x y] -> vst1_value(vcx, x) & vst1_value(vcx, y)
    [K"&&" xs...] -> allv(vst1_value, vcx, xs)
    [K"||" xs...] -> allv(vst1_value, vcx, xs)
    [K".&&" x y] -> vst1_value(vcx, x) & vst1_value(vcx, y)
    [K".||" x y] -> vst1_value(vcx, x) & vst1_value(vcx, y)
    (_, run=pass_or_err(vst1_arraylike, vcx, st), when=run.known) -> run.pass
    # value-producing const, global-=
    [K"const" [K"global" x]] -> vst1_const_assign(vcx, x)
    [K"global" [K"const" x]] -> vst1_const_assign(vcx, x)
    [K"const" x] -> !vcx.in_gscope ?
        fail(vcx, st, "unsupported `const` declaration on local variable") :
        vst1_const_assign(vcx, x)
    [K"global" [K"=" l r]] ->
        vst1_assign_lhs(vcx, l; disallow_type=!vcx.toplevel) &
        vst1_value(vcx, r)
    # syntax TODO: local is always OK as a value, but non-assigning should probably not be
    # TODO: fail if immediate toplevel?
    [K"local" xs...] -> allv(vst1_symdecl_or_assign, vcx, xs)

    # Forms not produced by the parser
    [K"inert" _] -> true
    [K"core"] -> true
    [K"top"] -> true
    [K"meta" _...] -> true # TODO documented forms, once we figure out how we'll deal with this
    [K"extension" [K"Symbol"] _...] ->
        (st[1].name_val in ("locals", "islocal", "isglobal") || fail(vcx, st, "unknown extension kind"))
    [K"toplevel" xs...] -> # contents will be unexpanded
        allv(valid_st0, with(vcx, :toplevel=>true, :in_gscope=>true), xs)
    [K"opaque_closure" argt lb ub [K"Bool"] lam] ->
        allv(vst1_value, vcx, [argt, lb, ub]) & vst1_lam(vcx, lam)
    [K"gc_preserve" x ids...] -> vst1_value(vcx, x) & allv(vst1_ident, vcx, ids)
    [K"gc_preserve_begin" ids...] -> allv(vst1_ident, vcx, ids)
    [K"gc_preserve_end" ids...] -> allv(vst1_ident, vcx, ids)
    # [K"thisfunction"] -> !vcx.toplevel && vcx.return_ok ||
    #     fail(vcx, st, "`thisfunction` is not defined in generators or outside of functions")
    [K"isdefined" [K"Identifier"]] -> true
    [K"lambda" [K"block" b1...] [K"block" b2...] [K"->" _...]] ->
        allv(vst1_ident, vcx, b1) &
        allv(vst1_ident, vcx, b2) &
        vst1_lam(vcx, st[3])
    [K"generated"] -> true
    ([K"foreigncall" f [K"static_eval" rt] [K"static_eval" argt_svec] args...],
     when=kind(f) in (K"Symbol", K"Identifier")) ->
        vst1_value(vcx, rt) & vst1_value(vcx, argt_svec) & allv(vst1_value, vcx, args)
    [K"cfunction" t [K"static_eval" fptr] [K"static_eval" rt] [K"static_eval" argt_svec] [K"Symbol"]] ->
        vst1_value(vcx, t) & vst1_value(vcx, fptr) & vst1_value(vcx, rt) & vst1_value(vcx, argt_svec)
    [K"cfunction" t fptr [K"static_eval" rt] [K"static_eval" argt_svec] [K"Symbol"]] ->
        vst1_value(vcx, t) & vst1_value(vcx, fptr) & vst1_value(vcx, rt) & vst1_value(vcx, argt_svec)
    [K"scope_block" x] -> vst1_value(vcx, x; need_value)

    # Only from macro expansions producing Expr(:toplevel, ...).  We don't want
    # to recurse on the contained expression since `K"escape"` can wrap nearly
    # any node.  This is OK since (1) if we're running `valid_st1`
    # pre-desugaring, this form is not recognized by desugaring and wrapped in a
    # `toplevel` anyway, so we'll see the expanded version later.  (2) If we're
    # running `valid_st0`, macros are not expanded, so this form won't appear.
    ([K"hygienic_scope" x [K"Value"] [K"Value"]]) ->
        vcx.unexpanded || fail(vcx, st, "`hygienic_scope` not valid after macro expansion")
    [K"hygienic_scope" x [K"Value"]] ->
        vcx.unexpanded || fail(vcx, st, "`hygienic_scope` not valid after macro expansion")

    # forms normalized by expand_forms_1, so not valid in st1.  TODO: we should
    # consider doing each of these normalizations before macro expansion rather
    # than after.
    ([K"juxtapose" xs...], when=vcx.unexpanded) -> allv(vst1_value, vcx, xs)
    ([K"cmdstring" x], when=vcx.unexpanded) -> vst1_value(vcx, x)
    ([K"char" [K"Char"]], when=vcx.unexpanded) -> true
    ([K"var" [K"Identifier"]], when=vcx.unexpanded) -> true

    # Invalid forms for which we want to produce detailed errors
    [K"..." _...] -> fail(vcx, st, "unexpected splat not in `call`, `tuple`, `curly`, or array expression")
    [K"parameters" _...] -> fail(vcx, st, "unexpected keyword-separating semicolon outside of call or tuple")
    [K"braces" _...] -> fail(vcx, st, "`braces` outside of `where` is reserved for future use")
    [K"bracescat" _...] -> fail(vcx, st, "`bracescat` is reserved for future use")
    [K"do" _...] -> fail(vcx, st, "unexpected `do` outside of `call`")
    [K"Placeholder"] -> fail(vcx, st, "all-underscore identifiers are write-only and their values cannot be used in expressions")
    [K"atomic" _...] -> fail(vcx, st, "unimplemented or unsupported `atomic` declaration")
    [K"::" x] -> fail(vcx, st, "`::` must be written `value::type` outside function argument lists")
    (_, when=need_value && kind(st) in KSet"symbolic_label symbolic_goto") ->
        fail(vcx, st, "misplaced `$(kind(st))` in value position")
    ([K"global" _...], when=need_value) ->
        fail(vcx, st, "global declaration doesn't read the variable and can't return a value")

    (_, run=pass_or_err(vst1_toplevel_only_value, vcx, st), when=run.known) ->
        run.pass && (vcx.toplevel || fail(vcx, st, "this syntax is only allowed in top level code"))
    _ -> false
end

vst1_toplevel_only_value(vcx::Validation1Context, st::SyntaxTree) = @stm st begin
    [K"module" name [K"block" xs...]] -> (
        vst1_ident(vcx, name) & allv(valid_st0, with(vcx, :toplevel=>true, :in_gscope=>true), xs))
    [K"macro" _...] -> vst1_macro(vcx, st)
    # The following return nothing, but are allowed as values
    [K"struct" sig [K"block" body...]] -> vst1_typesig(vcx, sig) &
        allv(vst1_struct_field, vcx, body)
    [K"abstract" sig] -> vst1_typesig(vcx, sig)
    [K"primitive" sig [K"Integer"]] -> vst1_typesig(vcx, sig)
    [K"primitive" sig n] -> vst1_typesig(vcx, sig) & vst1_value(vcx, n) # allowed?
    _ -> false
end

vst1_stmt(vcx::Validation1Context, st::SyntaxTree) = @stm st begin
    (_, run=pass_or_err(vst1_value, vcx, st; need_value=false), when=run.known) -> run.pass
    ([K"global" xs...], when=vcx.toplevel) -> allv(vst1_symdecl_or_assign, vcx, xs)
    ([K"global" xs...], when=!vcx.toplevel) -> allv(vst1_inner_global_decl, vcx, xs)
    [K"symbolic_label"] -> true
    [K"symbolic_goto"] -> true

    (_, run=pass_or_err(vst1_toplevel_only_stmt, vcx, st), when=run.known) ->
        run.pass && (vcx.toplevel || fail(vcx, st, "this syntax is only allowed in top level code"))
    _ -> fail(vcx, st, "invalid syntax: unknown kind `$(kind(st))` or number of arguments ($(numchildren(st)))")
end

vst1_inner_global_decl(vcx, st) = @stm st begin
    (_, when=cst1_ident(vcx, st)) -> true
    [K"=" l r] -> vst1_assign_lhs(vcx, l; disallow_type=true) & vst1_value(vcx, r)
    [K"function" _...] -> vst1_function(vcx, st) &&
        JuliaSyntax.has_flags(st, JuliaSyntax.SHORT_FORM_FUNCTION_FLAG)

    [K"::" _...] -> fail(vcx, st, "type declarations for global variables must be at top level, not inside a function")
    _ -> fail(vcx, st, "invalid global declaration: expected identifier or assignment")
end

vst1_toplevel_only_stmt(vcx::Validation1Context, st::SyntaxTree) = @stm st begin
    # Parsing is stricter (no "as" in no-colon using)
    [K"import" [K":" p1 ps...]] ->
        (vst1_importpath(vcx, p1; dots_ok=true) &
        allv(vst1_importpath, vcx, ps; dots_ok=false))
    [K"using"  [K":" p1 ps...]] ->
        (vst1_importpath(vcx, p1; dots_ok=true) &
        allv(vst1_importpath, vcx, ps; dots_ok=false))
    [K"import" ps...] -> allv(vst1_importpath, vcx, ps; dots_ok=true)
    [K"using"  ps...] -> allv(vst1_importpath, vcx, ps; dots_ok=true)
    [K"public" xs...] -> allv(vst1_ident, vcx, xs)
    [K"export" xs...] -> allv(vst1_ident, vcx, xs)
    [K"latestworld"] -> true
    [K"latestworld_if_toplevel"] -> true
    _ -> false
end

# @stm doesn't work so well with n dots and m identifiers
# one of:
# (as (importpath . . . x y z) ident)
#     (importpath . . . x y z)
# where y, z may be quoted for no reason (do we need to allow this?)
function vst1_importpath(vcx, st; dots_ok)
    ok = true
    path_components = @stm st begin
        [K"as" [K"importpath" xs...] as2] -> (
            if !vst1_ident(vcx, as2)
                fail(vcx, as2, "expected identifier after `as`")
                ok = false
            end; xs)
        [K"importpath" xs...] -> xs
    end
    seen_first = false
    for c in path_components
        if kind(c) === K"."
            if !dots_ok || seen_first
                ok = false
                fail(vcx, c, "unexpected `.` in import path")
            end
            continue
        end
        ok = ok && vst1_ident(vcx, seen_first && kind(c) === K"quote" ? c[1] : c)
        seen_first = true
    end
    !seen_first && fail(vcx, st, "expected identifier in `importpath`")
    return ok && seen_first
end

vst1_block(vcx, st; need_value=true) = @stm st begin
    [K"block"] -> true
    ([K"block" xs...], when=!need_value) -> allv(vst1_stmt, vcx, xs)
    [K"block" xs... val] -> allv(vst1_stmt, vcx, xs) & vst1_value(vcx, val)
    _ -> fail(vcx, st, "expected `block`")
end

vst1_else(vcx, st; need_value) = @stm st begin
    [K"block" _...] -> vst1_block(vcx, st; need_value)
    [K"elseif" cond t f] ->
        vst1_value(vcx, cond) & vst1_block(vcx, t; need_value) & vst1_else(vcx, f; need_value)
    _ -> vst1_value(vcx, st; need_value)
end

# TODO: catch and else are in value position
vst1_try(vcx, st) = @stm st begin
    [K"try" _] -> fail(vcx, st, "try without catch or finally")
    [K"try" b1 [K"catch" err body2...]] ->
        vst1_block(vcx, b1) &
        vst1_ident_lhs(vcx, err) &
        allv(vst1_stmt, vcx, body2)
    [K"try" b1 [K"else" body3...]] ->
        fail(vcx, st, "try without catch or finally")
    [K"try" b1 [K"finally" body4...]] ->
        vst1_block(vcx, b1) &
        allv(vst1_stmt, vcx, body4)
    [K"try" b1 [K"catch" err body2...] [K"else" body3...]] ->
        vst1_block(vcx, b1) &
        vst1_ident_lhs(vcx, err) &
        allv(vst1_stmt, vcx, body2) &
        allv(vst1_stmt, vcx, body3)
    [K"try" b1 [K"catch" err body2...] [K"finally" body4...]] ->
        vst1_block(vcx, b1) &
        vst1_ident_lhs(vcx, err) &
        allv(vst1_stmt, vcx, body2) &
        allv(vst1_stmt, vcx, body4)
    [K"try" b1 [K"else" body3...] [K"finally" body4...]] ->
        vst1_block(vcx, b1) &
        allv(vst1_stmt, vcx, body4)
    [K"try" b1 [K"catch" err body2...] [K"else" body3...] [K"finally" body4...]] ->
        vst1_block(vcx, b1) &
        vst1_ident_lhs(vcx, err) &
        allv(vst1_stmt, vcx, body2) &
        allv(vst1_stmt, vcx, body3) &
        allv(vst1_stmt, vcx, body4)
    _ -> fail(vcx, st, "malformed `try` expression")
end

# syntax TODO:
# - const is inoperative in the function case
# - single-arg const with no value (presumably to poison this name) was likely
#   not intended to work, and can only be produced by macros
vst1_const_assign(vcx, st) = @stm st begin
    (_, when=!vcx.toplevel) -> fail(vcx, st, "`const` declaration not allowed inside function")
    [K"=" l r] -> vst1_assign_lhs(vcx, l; in_const=true) & vst1_value(vcx, r)
    [K"function" _...] -> vst1_function(vcx, st) &&
        JuliaSyntax.has_flags(st, JuliaSyntax.SHORT_FORM_FUNCTION_FLAG)
    [K"Identifier"] -> true

    [K"local" _...] -> fail(vcx, st, "locals cannot be declarated `const`")
    _ -> fail(vcx, st, "expected assignment after `const`")
end

# We can't validate A.B in general (usually lowers to getproperty), but it shows
# up in a number of syntax special cases where we can.
vst1_dotpath(vcx, st) = @stm st begin
    [K"." l r] -> vst1_dotpath(vcx, l) & vst1_dot_rhs(vcx, r)
    [K"Value"] -> typeof(st.value) in (Module, GlobalRef)
    lhs -> vst1_ident(vcx, lhs)
end

vst1_dot_rhs(vcx, st) = (vcx.unexpanded ?
    kind(st) === K"Identifier" : kind(st) === K"Symbol") ||
    kind(st) === K"string" || # syntax TODO: disallow
    fail(vcx, st, "`(. a b)` requires symbol `b` after macro-expansion, or identifier before")

cst1_assign(vcx, st) = @stm st begin
    [K"=" l r] -> vst1_assign_lhs(vcx, l) & vst1_value(vcx, r)
    [K"function" _...] -> vst1_function(vcx, st) &&
        JuliaSyntax.has_flags(st, JuliaSyntax.SHORT_FORM_FUNCTION_FLAG)
    _ -> false
end

vst1_symdecl_or_assign(vcx, st) = cst1_assign(vcx, st) || vst1_symdecl(vcx, st)

vst1_symdecl(vcx, st) = @stm st begin
    (_, when=cst1_ident(vcx, st)) -> true
    [K"::" [K"Identifier"] t] -> vst1_value(vcx, t)
    _ -> fail(vcx, st, "expected identifier or `::`")
end

# ast TODO: Omit the `var` container at the parser level.  This would let us
# delete these entirely and just match [K"Identifier"] instead.
# TODO: A K"Value" globalref is often OK in place of an identifier; check usage
# of this function
vst1_ident(vcx, st) =
    cst1_ident(vcx, st) || fail(vcx, st, "expected identifier, got `$(kind(st))`")
cst1_ident(vcx, st) = @stm st begin
    [K"Identifier"] -> true
    [K"var" [K"Identifier"]] -> vcx.unexpanded ? true :
        fail(vcx, st, "`var` container not valid after macro expansion")
    _ -> false
end

vst1_ident_lhs(vcx, st) = @stm st begin
    [K"Placeholder"] -> true
    _ -> vst1_ident(vcx, st)
end

# no kws in macrocalls, but `do` is OK.
# TODO: we move `do` between st0 and st1...
vst1_call(vcx, st) = @stm st begin
    ([K"call" a0 op a1], when=(vcx.unexpanded && is_infix_op_call(st))) ->
        vst1_value(vcx, a0) &
        vst1_ident(vcx, op) &
        vst1_value(vcx, a1)
    ([K"call" a0 op], when=(vcx.unexpanded && is_postfix_op_call(st))) ->
        vst1_value(vcx, a0) &
        vst1_ident(vcx, op)
    [K"call" f [K"do" _...] args... [K"parameters" kwargs...]] ->
        vst1_value(vcx, f) &
        allv(vst1_call_arg, vcx, args) &
        allv(vst1_call_kwarg, vcx, kwargs) &
        vst1_do(vcx, st[2])
    [K"call" f args... [K"parameters" kwargs...]] ->
        vst1_value(vcx, f) &
        allv(vst1_call_arg, vcx, args) &
        allv(vst1_call_kwarg, vcx, kwargs)
    [K"call" f [K"do" _...] args...] ->
        vst1_value(vcx, f) &
        allv(vst1_call_arg, vcx, args) &
        vst1_do(vcx, st[2])
    [K"call" f args...] ->
        vst1_value(vcx, f) &
        allv(vst1_call_arg, vcx, args)
    _ -> fail(vcx, st, "invalid `call` form")
end

# unfortunate duplicate of the above
vst1_dotcall(vcx, st) = @stm st begin
    ([K"dotcall" a0 op a1], when=(vcx.unexpanded && is_infix_op_call(st))) ->
        vst1_value(vcx, a0) &
        vst1_ident(vcx, op) &
        vst1_value(vcx, a1)
    ([K"dotcall" a0 op], when=(vcx.unexpanded && is_postfix_op_call(st))) ->
        vst1_value(vcx, a0) &
        vst1_ident(vcx, op)
    [K"dotcall" f [K"do" _...] args... [K"parameters" kwargs...]] ->
        vst1_value(vcx, f) &
        allv(vst1_call_arg, vcx, args) &
        allv(vst1_call_kwarg, vcx, kwargs) &
        vst1_do(vcx, st[2])
    [K"dotcall" f args... [K"parameters" kwargs...]] ->
        vst1_value(vcx, f) &
        allv(vst1_call_arg, vcx, args) &
        allv(vst1_call_kwarg, vcx, kwargs)
    [K"dotcall" f [K"do" _...] args...] ->
        vst1_value(vcx, f) &
        allv(vst1_call_arg, vcx, args) &
        vst1_do(vcx, st[2])
    [K"dotcall" f args...] ->
        vst1_value(vcx, f) &
        allv(vst1_call_arg, vcx, args)
    _ -> fail(vcx, st, "invalid `call` form")
end

# Arg to call (not function decl), pre-semicolon.  This can be anything, but
# assignments (interpreted as kwargs) must have a simple LHS, and splat is OK.
vst1_call_arg(vcx, st) = @stm st begin
    [K"=" id val] -> vst1_ident(vcx, id) & vst1_value(vcx, val)
    [K"..." x] -> vst1_value(vcx, x) # complex assignment in here is OK
    _ -> vst1_value(vcx, st)
end

# Arg to `parameters` (post-semicolon) in a call (not function decl) can be:
# - ident
# - ident=value
# - :ident=>value
# - value...
vst1_call_kwarg(vcx, st) = @stm st begin
    (_, when=cst1_ident(vcx, st)) -> true
    [K"=" id val] -> vst1_ident(vcx, id) & vst1_value(vcx, val)
    # TODO: this call isn't necessarily infix, and we should check name_val is =>
    [K"call" [K"quote" id] arrow v] -> vst1_ident(vcx, id) &
        vst1_ident(vcx, arrow) & vst1_value(v)
    [K"..." x] -> vst1_value(vcx, x)
    _ -> fail(vcx, st, "malformed `parameters`; expected identifier, `=`, or, `...`")
end

vst1_lam(vcx, st) = @stm st begin
    [K"->" l r] ->
        vst1_lam_lhs(with(vcx, :return_ok=>false, :toplevel=>false, :in_gscope=>false), l) &
        vst1_stmt(with(vcx, :return_ok=>true, :toplevel=>false, :in_gscope=>false), r)
    _ -> false
end

vst1_lam_lhs(vcx, st) = @stm st begin
    [K"tuple" ps... [K"parameters" _...]] ->
        _calldecl_positionals(vcx, ps) & vst1_calldecl_kws(vcx, st[end])
    [K"tuple" ps...] -> _calldecl_positionals(vcx, ps)
    [K"where" ps t] -> vst1_lam_lhs(vcx, ps) & vst1_where_rhs(vcx, t)
    # ast TODO: This is handled badly in the parser
    [K"block" ps...] -> allv(vst1_param_kw, vcx, ps)
    _ -> fail(vcx, st, "malformed `->` expression")
end

vst1_do(vcx, st) = @stm st begin
    [K"do" [K"tuple" ps...] b] ->
        allv(vst1_param_req, with(vcx, :return_ok=>false, :toplevel=>false, :in_gscope=>false), ps) &
        vst1_block(with(vcx, :return_ok=>true, :toplevel=>false, :in_gscope=>false), b)
    _ -> fail(vcx, st, "malformed `do` expression")
end

vst1_function(vcx, st) = @stm st begin
    [K"function" name] -> vst1_ident(vcx, name)
    [K"function" callex body] ->
        vst1_function_calldecl(with(vcx, :return_ok=>false, :toplevel=>false, :in_gscope=>false), callex) &
        # usually a block, but not in the function-= case
        # TODO: should body be a value?
        vst1_stmt(with(vcx, :return_ok=>true, :toplevel=>false, :in_gscope=>false), body)
    _ -> fail(vcx, st, "malformed `function`")
end

# Note that we consistently refer to children of a declaring call as
# "parameters" rather than arguments (and children of a K"parameters" block as
# "keyword args/params") so we don't mix them up with children to a real call,
# whose valid forms are subtly different.

vst1_function_calldecl(vcx, st) = @stm st begin
    [K"where" callex tvs] ->
        vst1_function_calldecl(vcx, callex) & vst1_where_rhs(vcx, tvs)
    [K"::" callex rt] ->
        vst1_simple_calldecl(vcx, callex) & vst1_value(vcx, rt)
    _ -> vst1_simple_calldecl(vcx, st)
end

vst1_simple_calldecl(vcx, st; in_macro=false) = @stm st begin
    [K"call" f ps... [K"parameters" _...]] -> vst1_calldecl_name(vcx, f) &
        _calldecl_positionals(vcx, ps) &
        vst1_calldecl_kws(vcx, st[end])
    [K"call" f ps...] -> vst1_calldecl_name(vcx, f) &
        _calldecl_positionals(vcx, ps)

    # anonymous function syntax `function (x)` ?!
    [K"tuple" ps... [K"parameters" _...]] -> _calldecl_positionals(vcx, ps) &
        vst1_calldecl_kws(vcx, st[end])
    [K"tuple" ps...] -> _calldecl_positionals(vcx, ps)

    [K"dotcall" _...] -> fail(vcx, st, "cannot define function using `.` broadcast syntax")
    _ -> fail(vcx, st, "malformed `call` in function decl")
end

vst1_macro(vcx, st) = @stm st begin
    (_, when=!vcx.in_gscope) -> fail(vcx, st, "macro definition is not allowed in a local scope")
    [K"macro" m] -> vst1_ident(vcx, m)
    [K"macro" [K"call" _... [K"parameters" _...]] _...] ->
        fail(vcx, st[1][end], "macros cannot accept keyword arguments")
    [K"macro" [K"call" m ps...] body] ->
        let vcx = with(vcx, :return_ok=>false, :toplevel=>false, :in_gscope=>false)
            vst1_macro_calldecl_name(vcx, m) &
                _calldecl_positionals(vcx, ps) &
                vst1_block(with(vcx, :return_ok=>true), body)
        end
end

vst1_macro_calldecl_name(vcx, st) = @stm st begin
    (_, when=cst1_ident(vcx, st)) -> true
    [K"." l r] -> vst1_dotpath(vcx, l) & vst1_dot_rhs(vcx, r)
    _ -> fail(vcx, st, "invalid macro name")
end

vst1_calldecl_name(vcx, st) = @stm st begin
    (_, when=cst1_ident(vcx, st)) -> true
    [K"." l r] -> vst1_dotpath(vcx, l) & vst1_dot_rhs(vcx, r)
    [K"curly" t tvs...] -> vst1_calldecl_name(vcx, t) & allv(vst1_value, vcx, tvs)
    [K"Value"] -> true # GlobalRef works. Function? Type?
    # callable type
    [K"::" t] -> vst1_value(vcx, t)
    [K"::" x t] -> vst1_ident(vcx, x) & vst1_value(vcx, t)
    _ -> fail(vcx, st, "invalid function name")
end

# Check mandatory and optional positional params. Another case of @stm being too
# limited: `[required_param* opt_param* (= (... required_param) val)|(... required_param)?]`
function _calldecl_positionals(vcx, params)
    require_assign = false
    ok = true
    if !isempty(params)
        maybe_va = params[end]
        # (= (... required_param) val)
        if kind(maybe_va) === K"=" && numchildren(maybe_va) === 2
            ok &= vst1_splat_or_val(vcx, maybe_va[2])
            maybe_va = maybe_va[1]
        end
        # (... required_param)
        if kind(maybe_va) === K"..."
            numchildren(maybe_va) !== 1 && fail(vcx, maybe_va, "invalid `...` form")
            # TODO: can this actually be a tuple?
            ok &= vst1_param_req_or_tuple(vcx, maybe_va[1])
            params = params[1:end-1]
        end
    end
    for p in params
        if kind(p) === K"="
            require_assign = true
            ok &= vst1_param_opt(vcx, p)
        elseif kind(p) === K"..."
            ok = fail(vcx, p, "`...` may only be used on the final parameter")
        elseif require_assign # TODO: multi-syntaxtree error
            ok = fail(vcx, p, "all function parameters after an optional parameter must also be optional")
        else
            ok &= vst1_param_req_or_tuple(vcx, p)
        end
    end
    return ok
end

# destructuring args: function f(a, (x, y)) ...
vst1_param_req_or_tuple(vcx, st) = @stm st begin
    [K"::" [K"tuple" _...] t] ->
        vst1_simple_tuple_lhs(vcx, st[1]) & vst1_value(vcx, t)
    [K"tuple" _...] -> vst1_simple_tuple_lhs(vcx, st)
    _ -> vst1_param_req(vcx, st)
end

vst1_simple_tuple_lhs(vcx, st) = @stm st begin
    [K"tuple" xs...] -> allv(vst1_simple_tuple_lhs, vcx, xs)
    _ -> vst1_ident_lhs(vcx, st)
end

vst1_param_req(vcx, st) = @stm st begin
    (_, when=vst1_ident_lhs(with(vcx, :speculative=>true), st)) -> true
    [K"::" x t] -> vst1_ident_lhs(vcx, x) & vst1_value(vcx, t)
    [K"::" t] -> vst1_value(vcx, t)
    _ -> fail(vcx, st, "malformed positional param; expected identifier or `::`")
end

vst1_param_opt(vcx, st) = @stm st begin
    [K"=" id val] -> vst1_param_req_or_tuple(vcx, id) & vst1_value(vcx, val)
    _ -> fail(vcx, st, "malformed optional positional param; expected `=`")
end

vst1_calldecl_kws(vcx, st) = @stm st begin
    [K"parameters" kws... [K"..." varkw]] ->
        allv(vst1_param_kw, vcx, kws) & vst1_param_req(vcx, varkw)
    [K"parameters" kws...] -> allv(vst1_param_kw, vcx, kws)
end

vst1_param_kw(vcx, st) = @stm st begin
    (_, when=vst1_symdecl(with(vcx, :speculative=>true), st)) -> true
    [K"=" id val] -> vst1_symdecl(vcx, id) & vst1_value(vcx, val)
    [K"..." _...] -> fail(vcx, st, "`...` may only be used for the last keyword parameter")
    _ -> fail(vcx, st, "malformed keyword parameter; expected identifier, `=`, or `::`")
end

vst1_where_rhs(vcx, st) = @stm st begin
    [K"braces" tvs...] -> allv(vst1_typevar_decl, vcx, tvs)
    _ -> vst1_typevar_decl(vcx, st)
end

vst1_typevar_decl(vcx, st) = @stm st begin
    (_, when=cst1_ident(vcx, st)) -> true
    [K"<:" [K"Identifier"] old] -> vst1_value(vcx, old)
    [K">:" [K"Identifier"] old] -> vst1_value(vcx, old)
    ([K"comparison" old1 [K"Identifier"] [K"Identifier"] [K"Identifier"] old2],
     when=st[2].name_val===st[4].name_val && st[2].name_val in ("<:", ">:")) ->
         vst1_value(vcx, old1) & vst1_value(vcx, old2)

    [K"<:" x _] -> fail(vcx, x, "expected type name")
    [K">:" x _] -> fail(vcx, x, "expected type name")
    [K"comparison" _...] -> fail(vcx, st, "expected `lb <: type_name <: ub` or `ub >: type_name >: lb`")
    _ -> fail(vcx, st, "expected type name or type bounds")
end

vst1_typesig(vcx, st) = @stm st begin
    (_, when=cst1_ident(vcx, st)) -> true
    [K"<:" [K"curly" name tvs...] super] ->
        vst1_ident(vcx, name) &
        vst1_value(vcx, super) &
        allv(vst1_typevar_decl, vcx, tvs)
    [K"curly" name tvs...] -> vst1_ident(vcx, name) & allv(vst1_typevar_decl, vcx, tvs)
    [K"<:" name super] -> vst1_ident(vcx, name) & vst1_value(vcx, super)
    _ -> fail(vcx, st, "invalid type signature")
end

# normal, non-lhs curly may have implicit `(<: t)`
vst1_value_curly_typevar(vcx, st) = @stm st begin
    [K"<:" t] -> vst1_splat_or_val(vcx, t)
    [K">:" t] -> vst1_splat_or_val(vcx, t)
    _ -> vst1_splat_or_val(vcx, st)
end

vst1_struct_field(vcx, st) = @stm st begin
    (_, when=cst1_ident(vcx, st)) -> true
    [K"block" x] -> vst1_struct_field(vcx, x)
    [K"::" x t] -> vst1_struct_field(vcx, x) & vst1_value(vcx, t)
    [K"const" x] -> vst1_struct_field(vcx, x)
    [K"atomic" x] -> vst1_struct_field(vcx, x)
    _ -> vst1_stmt(vcx, st)
end

# syntax TODO: (local/global (= lhs rhs)) forms should probably reject the same lhss as const (ref and .)
# TODO: We can do some destructuring checks here (e.g. fail `(a,b,c) = (1,2)`)
# compat:
# - call (only within a tuple using JuliaSyntax) can declare a function with
#   arguments, but can't use them on the rhs
# - in curly, typevars are checked for structure, but not used.
vst1_assign_lhs(vcx, st; in_const=false, in_tuple=false, disallow_type=false) = @stm st begin
    [K"tuple" [K"parameters" xs...]] -> allv(vst1_symdecl, vcx, xs)
    [K"tuple" xs...] ->
        allv(vst1_assign_lhs, vcx, xs; in_const, in_tuple=true) &
        (count(kind(x)===K"..." for x in xs) <= 1 ||
        fail(vcx, st, "multiple `...` in destructuring assignment are ambiguous"))
    # Parser produces this in too many places
    # [K"call" _...] ->
    #     fail(vcx, st, "`(= (call ...) ...)` syntax is deprecated, use `(function (call ...) ...)`")
    # type-annotated tuple segfaults, haha
    # [K"::" [K"tuple" _...] t] -> ???
    _ -> vst1_assign_lhs_nontuple(vcx, st; in_const, in_tuple)
end
vst1_assign_lhs_nontuple(vcx, st; in_const=false, in_tuple=false, disallow_type=false) = @stm st begin
    (_, when=vst1_ident_lhs(with(vcx, :speculative=>true), st)) -> true
    (_, when=(in_const && kind(st) in (K".", K"ref"))) ->
        fail(vcx, st, "cannot declare this form constant")
    ([K"Value"], when=st.value isa GlobalRef) -> true
    ([K"::" x t], when=!disallow_type) ->
        vst1_assign_lhs(vcx, x; in_const, in_tuple) & vst1_value(vcx, t)
    [K"call" _...] -> vst1_function_calldecl(vcx, st)
    [K"." x y] -> vst1_value(vcx, x) & vst1_dot_rhs(vcx, y)
    [K"..." x] -> !in_tuple ?
        fail(vcx, st, "splat on left side of assignment must be in a tuple") :
        vst1_assign_lhs(vcx, x; in_const, in_tuple)
    [K"ref" x is...] -> vst1_assign_lhs_nontuple(vcx, x; in_const, in_tuple) &
        allv(vst1_splat_or_val, vcx, is)
    [K"curly" t tvs...] -> vst1_ident_lhs(vcx, t) &
        allv(vst1_typevar_decl, vcx, tvs)

    # errors
    ([K"::" _...], when=disallow_type) ->
        fail(vcx, st, "type declarations for global variables must be at top level, not inside a function")
    [K"typed_hcat" _...] -> fail(vcx, st, "invalid spacing on left side of indexed assignment")
    [K"typed_vcat" _...] -> fail(vcx, st, "unexpected `;` in left side of indexed assignment")
    [K"typed_ncat" _...] -> fail(vcx, st, "unexpected `;` in left side of indexed assignment")
    ([K"parameters" _...], when=in_tuple) ->
        fail(vcx, st, "property destructuring must use a single `;` before the property names, eg `(; a, b) = rhs`")
    (_, when=(kind(st) in KSet"vect hcat vcat ncat")) -> fail(vcx, st, "use `(a, b) = ...` to assign multiple values")
    _ -> fail(vcx, st, "invalid `$(kind(st))` on left side of assignment")
end

# dot-assign with placeholders in an arraylike lhs throws a syntax error
vst1_dotassign_lhs(vcx, st) =
    vst1_arraylike(with(vcx, :speculative=>true), st) || vst1_assign_lhs(vcx, st)

vst1_arraylike(vcx, st) = @stm st begin
    # TODO: more validation is possible here, e.g. when row/nrow can/can't show up in ncat
    [K"vect" xs...] -> allv(vst1_splat_or_val, vcx, xs)
    [K"hcat" xs...] -> allv(vst1_splat_or_val, vcx, xs)
    [K"vcat" xs...] -> allv(vst1_splat_or_val, vcx, xs)
    [K"ncat" xs...] -> allv(vst1_splat_or_val, vcx, xs)
    [K"ref" x is...] ->        vst1_value(vcx, x) & allv(vst1_splat_or_val, vcx, is)
    [K"typed_hcat" t xs...] -> vst1_value(vcx, t) & allv(vst1_splat_or_val, vcx, xs)
    [K"typed_vcat" t xs...] -> vst1_value(vcx, t) & allv(vst1_splat_or_val, vcx, xs)
    [K"typed_ncat" t xs...] -> vst1_value(vcx, t) & allv(vst1_splat_or_val, vcx, xs)
    [K"row" xs...] -> allv(vst1_splat_or_val, vcx, xs)
    [K"nrow" xs...] -> allv(vst1_splat_or_val, vcx, xs)
    _ -> false
end

# TODO: Are there things we can rule out from appearing in `...`?
vst1_splat_or_val(vcx, st) = @stm st begin
    [K"..." x] -> vst1_value(vcx, x)
    [K"..." _...] -> fail("expected one argument to `...`")
    _ -> vst1_value(vcx, st)
end

function vst1_generator(vcx, st)
    vcx = with(vcx, :return_ok=>false, :toplevel=>false, :in_gscope=>false)
    return @stm st begin
        [K"generator" val its...] ->
            vst1_value(vcx, val) &
            allv(vst1_iterspec, vcx, its)
        _ -> fail(vcx, st, "malformed `generator`")
    end
end

vst1_iterspec(vcx, st) = @stm st begin
    [K"filter" [K"iteration" is...] cond] -> allv(vst1_iter, vcx, is) & vst1_value(vcx, cond)
    [K"iteration" is...] -> allv(vst1_iter, vcx, is)
    _ -> fail(vcx, st, "malformed `iteration`")
end

vst1_iter(vcx, st) = @stm st begin
    [K"in" [K"outer" i] v] -> vst1_assign_lhs(vcx, i) & vst1_value(vcx, v)
    [K"in" i v] -> vst1_assign_lhs(vcx, i) & vst1_value(vcx, v)
    _ -> fail(vcx, st, "malformed `in`")
end

vst1_documented(vcx, st) = @stm st begin
    (_, when=kind(st) in KSet"function macro = struct abstract primitive const global Symbol inert module") ->
        vst1_stmt(vcx, st)
    # doc-only cases
    (_, when=kind(st) in KSet". Identifier tuple") -> vst1_stmt(vcx, st)
    (callex, when=vst1_function_calldecl(with(vcx, :speculative=>true), st)) -> true
    _ -> fail(vcx, st, "`$(kind(st))` cannot be annotated with a docstring")
end

"""
For convenience, much of the validation code for st0 (non-macro-expanded trees) is
shared with that for st1 (macro-expanded trees).  The main differences:
- quote/unquote is valid in st0 but not st1
- macrocalls are valid in st0 but not st1
- any of the ad-hoc pre-desugaring we do in expand_forms_1

Even though st0 should usually be limited to parser output, `valid_st0` allows a
superset of `vst1_stmt` to allow for validation of partially-expanded trees.
"""
function valid_st0(st::SyntaxTree)
    vcx = with(Validation1Context(), :unexpanded=>true)
    valid = vst1_stmt(vcx, st)
    for e in vcx.errors
        showerror(stdout, LoweringError(e.sts[1], e.msg))
        for st_ in e.sts[2:end]; show(st_); end
        printstyled("---------------------------------\n"; color=:red)
    end
    return valid
end
valid_st0(vcx, st) = @stm st begin
    _ -> vst1_stmt(with(vcx, :unexpanded=>true), st)
end

"""
TODO: While we can't validate any arguments to a macrocall in general, it would
make sense to check usage for things like @ccall.
"""
vst0_macrocall(vcx, st) = @stm st begin
    [K"macrocall" name args...] -> vst0_macro_name(vcx, name)
    _ -> false
end

vst0_quoted(vcx, st) = @stm st begin
    ([K"$" x], when=vcx.quote_level===1) -> valid_st0(with(vcx, :quote_level=>0), x)
    [K"$" x] -> vst0_quoted(with(vcx, :quote_level=>vcx.quote_level-1), x)
    [K"quote" x] -> vst0_quoted(with(vcx, :quote_level=>vcx.quote_level+1), x)
    _ -> allv(vst0_quoted, vcx, children(st))
end

# Currently julia allows arbitrary top-level code in the first argument of a
# macrocall.  It's probably OK to restrict this.
vst0_macro_name(vcx, st) = @stm st begin
    [K"." modpath [K"macro_name" mname]] -> (vst1_dotpath(vcx, modpath) & vst1_ident(vcx, mname))
    [K"macro_name" [K"." modpath mname]] -> (vst1_dotpath(vcx, modpath) & vst1_ident(vcx, mname))
    [K"Value"] -> true
    _ -> fail(vcx, st, "invalid macro name")
end

# Non-lazy `&` to fetch errors from all subtrees in the iterable
function allv(f, vcx, itr; kws...)
    ok = true
    for i in itr
        ok &= f(vcx, i; kws...)
    end
    return ok
end

# `known` is true if validation passes or knows what's wrong; false otherwise.
# Allows for a "match if `vst1_foo` knows what this is supposed to be" pattern:
#
#     (_, run=pass_or_err(vst1_foo, vcx, st), when=run.known) -> run.pass
#
# which is similar to splicing in all cases from `vst1_foo` that either pass or
# produce an error (i.e. `_ -> false` cases are ignored).
function pass_or_err(f, vcx, st; kws...)
    n_err = length(vcx.errors)
    pass = f(vcx, st; kws...)
    known = pass || length(vcx.errors) > n_err
    return (; known, pass)
end

function fail(vcx::Validation1Context, st::SyntaxTree, msg="invalid syntax")
    if !vcx.speculative
        push!(vcx.errors, ValidationDiagnostic(st, msg))
    end
    return false
end

vtodo(vcx, st, line=0) = (push!(vcx.errors, ValidationDiagnostic(st, "TODO: line $line")); false)
