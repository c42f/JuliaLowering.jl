@testset "SyntaxGraph attrs" begin
    st = parsestmt(SyntaxTree, "function foo end")
    g_init = JuliaLowering.unfreeze_attrs(st._graph)
    gf1 = JuliaLowering.freeze_attrs(g_init)
    gu1 = JuliaLowering.unfreeze_attrs(gf1)

    # Check that freeze/unfreeze do their jobs
    @test gf1.attributes isa NamedTuple
    @test gu1.attributes isa Dict
    @test Set(keys(gf1.attributes)) == Set(keys(gu1.attributes))

    # ensure_attributes
    gf2 = JuliaLowering.ensure_attributes(gf1, test_attr=Symbol, foo=Type)
    gu2 = JuliaLowering.ensure_attributes(gu1, test_attr=Symbol, foo=Type)
    # returns a graph with the same attribute storage
    @test gf2.attributes isa NamedTuple
    @test gu2.attributes isa Dict
    # does its job
    @test (:test_attr, Symbol) in JuliaLowering.attrtypes(gf2)
    @test (:foo, Type) in JuliaLowering.attrtypes(gf2)
    @test Set(keys(gf2.attributes)) == Set(keys(gu2.attributes))
    # no mutation
    @test !((:test_attr, Symbol) in JuliaLowering.attrtypes(gf1))
    @test !((:foo, Type) in JuliaLowering.attrtypes(gf1))
    @test Set(keys(gf1.attributes)) == Set(keys(gu1.attributes))

    # delete_attributes
    gf3 = JuliaLowering.delete_attributes(gf2, :test_attr, :foo)
    gu3 = JuliaLowering.delete_attributes(gu2, :test_attr, :foo)
    # returns a graph with the same attribute storage
    @test gf3.attributes isa NamedTuple
    @test gu3.attributes isa Dict
    # does its job
    @test !((:test_attr, Symbol) in JuliaLowering.attrtypes(gf3))
    @test !((:foo, Type) in JuliaLowering.attrtypes(gf3))
    @test Set(keys(gf3.attributes)) == Set(keys(gu3.attributes))
    # no mutation
    @test (:test_attr, Symbol) in JuliaLowering.attrtypes(gf2)
    @test (:foo, Type) in JuliaLowering.attrtypes(gf2)
    @test Set(keys(gf2.attributes)) == Set(keys(gu2.attributes))
end

@testset "SyntaxTree" begin
    # Expr conversion
    @test Expr(parsestmt(SyntaxTree, "begin a + b ; c end", filename="none")) ==
        Meta.parse("begin a + b ; c end")

    tree1 = JuliaLowering.@SyntaxTree :(some_unique_identifier)
    @test tree1 isa SyntaxTree
    @test kind(tree1) == K"Identifier"
    @test tree1.name_val == "some_unique_identifier"

    tree2 = JuliaLowering.@SyntaxTree quote
        x
        $tree1
    end
    @test tree2 isa SyntaxTree
    @test kind(tree2) == K"block"
    @test kind(tree2[1]) == K"Identifier" && tree2[1].name_val == "x"
    @test kind(tree2[2]) == K"Identifier" && tree2[2].name_val == "some_unique_identifier"
end
