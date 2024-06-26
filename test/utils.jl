using Test

using JuliaLowering:
    SyntaxGraph, newnode!, ensure_attributes!,
    Kind, SourceRef, SyntaxTree, NodeId,
    makenode, makeleaf, setattr!, sethead!,
    haschildren, numchildren, children

function _ast_test_graph()
    graph = SyntaxGraph()
    ensure_attributes!(graph,
                       kind=Kind, source=Union{SourceRef,NodeId,LineNumberNode},
                       var_id=Int, value=Any, name_val=String)
end

function _source_node(graph, src)
    id = newnode!(graph)
    sethead!(graph, id, K"None")
    setattr!(graph, id, source=src)
    SyntaxTree(graph, id)
end

macro ast_(tree)
    defs = []
    ex = JuliaLowering._expand_ast_tree(defs, :graph, :srcref, tree)
    quote
        graph = _ast_test_graph()
        srcref = _source_node(graph, $(QuoteNode(__source__)))
        $(defs...)
        $ex
    end
end

function ~(ex1, ex2)
    if kind(ex1) != kind(ex2) || haschildren(ex1) != haschildren(ex2)
        return false
    end
    if haschildren(ex1)
        if numchildren(ex1) != numchildren(ex2)
            return false
        end
        return all(c1 ~ c2 for (c1,c2) in zip(children(ex1), children(ex2)))
    else
        return get(ex1, :value,    nothing) == get(ex2, :value,    nothing) &&
               get(ex1, :name_val, nothing) == get(ex2, :name_val, nothing)
    end
end


#-------------------------------------------------------------------------------
function _format_as_ast_macro(io, ex, indent)
    k = kind(ex)
    kind_str = repr(k)
    if haschildren(ex)
        println(io, indent, "[", kind_str)
        ind2 = indent*"    "
        for c in children(ex)
            _format_as_ast_macro(io, c, ind2)
        end
        println(io, indent, "]")
    else
        val_str = if k == K"Identifier" || k == K"core" || k == K"top"
            repr(ex.name_val)
        elseif k == K"SSAValue"
            repr(ex.var_id)
        else
            repr(get(ex, :value, nothing))
        end
        println(io, indent, val_str, "::", kind_str)
    end
end

function format_as_ast_macro(io::IO, ex)
    print(io, "@ast_ ")
    _format_as_ast_macro(io, ex, "")
end

"""
    format_as_ast_macro(ex)

Format AST `ex` as a Juila source code call to the `@ast_` macro for generating
test case comparisons with the `~` function.
"""
format_as_ast_macro(ex) = format_as_ast_macro(stdout, ex)

#-------------------------------------------------------------------------------

# Test tools

function match_ir_test_case(case_str)
    m = match(r"# *([^\n]*)\n((?:.|\n)*)#----*\n((?:.|\n)*)"m, strip(case_str))
    if isnothing(m)
        error("Malformatted IR test case:\n$(repr(case_str))")
    end
    (name=strip(m[1]), input=strip(m[2]), output=strip(m[3]))
end

function format_ir_test_case(mod, input)
    ex = parsestmt(SyntaxTree, input)
    x = JuliaLowering.lower(mod, ex)
    output = strip(sprint(JuliaLowering.print_ir, x))
    output = replace(output, string(mod)=>"TestMod")
end

function test_ir_cases(filename)
    str = read(filename, String)
    cases = [match_ir_test_case(s) for s in split(str, r"####*") if strip(s) != ""]

    mod = Module(:TestMod)
    for (name,input,ref) in cases
        output = format_ir_test_case(mod, input)
        @testset "$name" begin
            if output != ref
                # Do our own error dumping, as @test will 
                @error "Test \"$name\" failed" output=Text(output) ref=Text(ref)
            end
            @test output == ref
        end
    end
end

