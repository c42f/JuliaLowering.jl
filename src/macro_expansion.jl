# Lowering pass 1: Macro expansion, simple normalizations and quote expansion

"""
A `ScopeLayer` is a mechanism for automatic hygienic macros; every identifier
is assigned to a particular layer and can only match against bindings which are
themselves part of that layer.

Normal code contains a single scope layer, whereas each macro expansion
generates a new layer.
"""
struct ScopeLayer
    id::LayerId
    mod::Module
    is_macro_expansion::Bool # FIXME
end

struct MacroExpansionContext{GraphType} <: AbstractLoweringContext
    graph::GraphType
    bindings::Bindings
    scope_layers::Vector{ScopeLayer}
    current_layer::ScopeLayer
end

#--------------------------------------------------
# Expansion of quoted expressions
function collect_unquoted!(ctx, unquoted, ex, depth)
    if kind(ex) == K"$" && depth == 0
        # children(ex) is usually length 1, but for double interpolation it may
        # be longer and the children may contain K"..." expressions. Wrapping
        # in a tuple groups the arguments together correctly in those cases.
        push!(unquoted, @ast ctx ex [K"tuple" children(ex)...])
    else
        inner_depth = kind(ex) == K"quote" ? depth + 1 :
                      kind(ex) == K"$"     ? depth - 1 :
                      depth
        for e in children(ex)
            collect_unquoted!(ctx, unquoted, e, inner_depth)
        end
    end
    return unquoted
end

function expand_quote(ctx, ex)
    unquoted = SyntaxTree[]
    collect_unquoted!(ctx, unquoted, ex, 0)
    # Unlike user-defined macro expansion, we don't call append_sourceref for
    # the entire expression produced by `quote` expansion. We could, but it
    # seems unnecessary for `quote` because the surface syntax is a transparent
    # representation of the expansion process. However, it's useful to add the
    # extra srcref in a more targetted way for $ interpolations inside
    # interpolate_ast, so we do that there.
    #
    # In principle, particular user-defined macros could opt into a similar
    # mechanism.
    #
    # TODO: Should we try adding a srcref to the `quote` node only for the
    # extra syntax generated by expand_quote so srcref essentially becomes
    # (ex, @HERE) ?
    @ast ctx ex [K"call"
        interpolate_ast::K"Value"
        [K"inert" ex]
        unquoted...
    ]
end

#--------------------------------------------------
struct MacroContext <: AbstractLoweringContext
    graph::SyntaxGraph
    macroname::SyntaxTree
    scope_layer::ScopeLayer
end

function adopt_scope(ex, ctx::MacroContext)
    adopt_scope(ex, ctx.scope_layer.id)
end

struct MacroExpansionError
    context::Union{Nothing,MacroContext}
    ex::SyntaxTree
    msg::String
    position::Symbol
end

"""
`position` - the source position relative to the node - may be `:begin` or `:end` or `:all`
"""
function MacroExpansionError(ex::SyntaxTree, msg::AbstractString; position=:all)
    MacroExpansionError(nothing, ex, msg, position)
end

function Base.showerror(io::IO, exc::MacroExpansionError)
    print(io, "MacroExpansionError")
    ctx = exc.context
    if !isnothing(ctx)
        print(io, " while expanding ", ctx.macroname,
              " in module ", ctx.scope_layer.mod)
    end
    print(io, ":\n")
    # TODO: Display niceties:
    # * Show the full provenance tree somehow, in addition to the primary
    #   source location we're showing here?
    # * What if the expression doesn't arise from a source file?
    # * How to deal with highlighting trivia? Could provide a token kind or
    #   child position within the raw tree? How to abstract this??
    src = sourceref(exc.ex)
    fb = first_byte(src)
    lb = last_byte(src)
    pos = exc.position
    byterange = pos == :all     ? (fb:lb)   :
                pos == :begin   ? (fb:fb-1) :
                pos == :end     ? (lb+1:lb) :
                error("Unknown position $pos")
    highlight(io, src.file, byterange, note=exc.msg)
end

function set_scope_layer(ctx, ex, layer_id, force)
    k = kind(ex)
    scope_layer = force ? layer_id : get(ex, :scope_layer, layer_id)
    if k == K"module" || k == K"toplevel" || k == K"inert"
        makenode(ctx, ex, ex, children(ex);
                 scope_layer=scope_layer)
    elseif k == K"."
        makenode(ctx, ex, ex, set_scope_layer(ctx, ex[1], layer_id, force), ex[2],
                 scope_layer=scope_layer)
    elseif haschildren(ex)
        mapchildren(e->set_scope_layer(ctx, e, layer_id, force), ctx, ex;
                    scope_layer=scope_layer)
    else
        makeleaf(ctx, ex, ex;
                 scope_layer=scope_layer)
    end
end

function eval_macro_name(ctx, ex)
    # `ex1` might contain a nontrivial mix of scope layers so we can't just
    # `eval()` it, as it's already been partially lowered by this point.
    # Instead, we repeat the latter parts of `lower()` here.
    ex1 = expand_forms_1(ctx, ex)
    ctx2, ex2 = expand_forms_2(ctx, ex1)
    ctx3, ex3 = resolve_scopes!(ctx2, ex2)
    ctx4, ex4 = linearize_ir(ctx3, ex3)
    mod = ctx.current_layer.mod
    expr_form = to_lowered_expr(mod, ex4.bindings, ex4)
    eval(mod, expr_form)
end

function expand_macro(ctx, ex)
    @assert kind(ex) == K"macrocall"

    macname = ex[1]
    macfunc = eval_macro_name(ctx, macname)
    # Macro call arguments may be either
    # * Unprocessed by the macro expansion pass
    # * Previously processed, but spliced into a further macro call emitted by
    #   a macro expansion.
    # In either case, we need to set any unset scope layers before passing the
    # arguments to the macro call.
    macro_args = [set_scope_layer(ctx, e, ctx.current_layer.id, false)
                  for e in children(ex)[2:end]]
    mctx = MacroContext(ctx.graph, macname, ctx.current_layer)
    expanded = try
        # TODO: Allow invoking old-style macros for compat
        invokelatest(macfunc, mctx, macro_args...)
    catch exc
        if exc isa MacroExpansionError
            # Add context to the error.
            # TODO: Using rethrow() is kinda ugh. Is there a way to avoid it?
            rethrow(MacroExpansionError(mctx, exc.ex, exc.msg, exc.position))
        else
            throw(MacroExpansionError(mctx, ex, "Error expanding macro", :all))
        end
    end

    if expanded isa SyntaxTree
        if !is_compatible_graph(ctx, expanded)
            # If the macro has produced syntax outside the macro context, copy it over.
            # TODO: Do we expect this always to happen?  What is the API for access
            # to the macro expansion context?
            expanded = copy_ast(ctx, expanded)
        end
        expanded = append_sourceref(ctx, expanded, ex)
        new_layer = ScopeLayer(length(ctx.scope_layers)+1, parentmodule(macfunc), true)
        push!(ctx.scope_layers, new_layer)
        inner_ctx = MacroExpansionContext(ctx.graph, ctx.bindings, ctx.scope_layers, new_layer)
        expanded = expand_forms_1(inner_ctx, expanded)
    else
        expanded = @ast ctx ex expanded::K"Value"
    end
    return expanded
end

# Add a secondary source of provenance to each expression in the tree `ex`.
function append_sourceref(ctx, ex, secondary_prov)
    srcref = (ex, secondary_prov)
    if haschildren(ex)
        if kind(ex) == K"macrocall"
            makenode(ctx, srcref, ex, children(ex)...)
        else
            makenode(ctx, srcref, ex,
                     map(e->append_sourceref(ctx, e, secondary_prov), children(ex))...)
        end
    else
        makeleaf(ctx, srcref, ex)
    end
end

"""
Lowering pass 1

This pass contains some simple expansion to make the rest of desugaring easier
to write and expands user defined macros. Macros see the surface syntax, so
need to be dealt with before other lowering.

* Does identifier normalization
* Strips semantically irrelevant "container" nodes like parentheses
* Expands macros
* Processes quoted syntax turning `K"quote"` into `K"inert"` (eg, expanding
  interpolations)
"""
function expand_forms_1(ctx::MacroExpansionContext, ex::SyntaxTree)
    k = kind(ex)
    if k == K"Identifier" && all(==('_'), ex.name_val)
        @ast ctx ex ex=>K"Placeholder"
    elseif k == K"true" || k == K"false"
        # FIXME: Move this upstream into JuliaSyntax
        @ast ctx ex (k == K"true")::K"Bool"
    elseif k == K"Identifier" || k == K"MacroName" || k == K"StringMacroName" ||
            (is_operator(k) && !haschildren(ex)) # <- TODO: fix upstream: make operator *tokens* into identifiers
        layerid = get(ex, :scope_layer, ctx.current_layer.id)
        makeleaf(ctx, ex, ex, kind=K"Identifier", scope_layer=layerid)
    elseif k == K"var" || k == K"char" || k == K"parens"
        # Strip "container" nodes
        @chk numchildren(ex) == 1
        expand_forms_1(ctx, ex[1])
    elseif k == K"quote"
        @chk numchildren(ex) == 1
        # TODO: Upstream should set a general flag for detecting parenthesized
        # expressions so we don't need to dig into `green_tree` here. Ugh!
        plain_symbol = has_flags(ex, JuliaSyntax.COLON_QUOTE) && 
                       kind(ex[1]) == K"Identifier" &&
                       (sr = sourceref(ex); sr isa SourceRef && kind(sr.green_tree[2]) != K"parens")
        if plain_symbol
            # As a compromise for compatibility, we treat non-parenthesized
            # colon quoted identifiers like `:x` as plain Symbol literals
            # because these are ubiquitiously used in Julia programs as ad hoc
            # enum-like entities rather than pieces of AST.
            @ast ctx ex[1] ex[1]=>K"Symbol"
        else
            expand_forms_1(ctx, expand_quote(ctx, ex[1]))
        end
    elseif k == K"macrocall"
        expand_macro(ctx, ex)
    elseif k == K"module" || k == K"toplevel" || k == K"inert"
        ex
    elseif !haschildren(ex)
        ex
    else
        mapchildren(e->expand_forms_1(ctx,e), ctx, ex)
    end
end

function expand_forms_1(mod::Module, ex::SyntaxTree)
    graph = ensure_attributes(syntax_graph(ex),
                              var_id=IdTag,
                              scope_layer=LayerId,
                              __macro_ctx__=Nothing)
    layers = ScopeLayer[ScopeLayer(1, mod, false)]
    ctx = MacroExpansionContext(graph, Bindings(), layers, layers[1])
    ex2 = expand_forms_1(ctx, reparent(ctx, ex))
    graph2 = delete_attributes(graph, :__macro_ctx__)
    # TODO: Returning the context with pass-specific mutable data is a bad way
    # to carry state into the next pass.
    ctx2 = MacroExpansionContext(graph2, ctx.bindings, ctx.scope_layers,
                                 ctx.current_layer)
    return ctx2, reparent(ctx2, ex2)
end

