
# The following kinds are used in intermediate forms by lowering but are not
# part of the surface syntax
function _register_kinds()
    JuliaSyntax.register_kinds!(JuliaLowering, 1, [
        "BEGIN_LOWERING_KINDS"
            # Compiler metadata hints
            "meta"
            "extension"
            # A literal Julia value of any kind, as might be inserted by the AST
            # during macro expansion
            "Value"
            # TODO: Emit "true" and "false" tokens as K"Bool" in parser to
            # harmonize with K"Int" etc?
            "Bool"
            # An identifier composed entirely of underscores
            "Placeholder"
            # A (quoted) `Symbol`
            "Symbol"
            # TODO: Use `meta` for inbounds and loopinfo etc?
            "inbounds"
            "inline"
            "noinline"
            "loopinfo"
            # Identifier for a value which is only assigned once
            "SSAValue"
            # Unique identifying integer for bindings (of variables, constants, etc)
            "BindingId"
            # Scope expressions `(hygienic_scope ex s)` mean `ex` should be
            # interpreted as being in scope `s`.
            "hygienic_scope"
            # Various heads harvested from flisp lowering.
            # (TODO: May or may not need all these - assess later)
            "break_block"
            "scope_block"
            "local_def"
            "_while"
            "_do_while"
            "with_static_parameters"
            "top"
            "core"
            "toplevel_butfirst"
            "thunk"
            "lambda"
            "moved_local"
            "the_exception"
            "foreigncall"
            "new"
            "globalref"
            "outerref"
            "enter"
            "leave"
            "label"
            "symbolic_label"
            "symbolic_goto"
            "goto"
            "gotoifnot"
            "trycatchelse"
            "tryfinally"
            "method"
            "slot"
            "unnecessary"
            "decl"
        "END_LOWERING_KINDS"
    ])
end
