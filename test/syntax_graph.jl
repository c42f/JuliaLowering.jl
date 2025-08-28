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
    @test (:test_attr=>Symbol) in JuliaLowering.attrdefs(gf2)
    @test (:foo=>Type) in JuliaLowering.attrdefs(gf2)
    @test Set(keys(gf2.attributes)) == Set(keys(gu2.attributes))
    # no mutation
    @test !((:test_attr=>Symbol) in JuliaLowering.attrdefs(gf1))
    @test !((:foo=>Type) in JuliaLowering.attrdefs(gf1))
    @test Set(keys(gf1.attributes)) == Set(keys(gu1.attributes))

    # delete_attributes
    gf3 = JuliaLowering.delete_attributes(gf2, :test_attr, :foo)
    gu3 = JuliaLowering.delete_attributes(gu2, :test_attr, :foo)
    # returns a graph with the same attribute storage
    @test gf3.attributes isa NamedTuple
    @test gu3.attributes isa Dict
    # does its job
    @test !((:test_attr=>Symbol) in JuliaLowering.attrdefs(gf3))
    @test !((:foo=>Type) in JuliaLowering.attrdefs(gf3))
    @test Set(keys(gf3.attributes)) == Set(keys(gu3.attributes))
    # no mutation
    @test (:test_attr=>Symbol) in JuliaLowering.attrdefs(gf2)
    @test (:foo=>Type) in JuliaLowering.attrdefs(gf2)
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

    "For filling required attrs in graphs created by hand"
    function testgraph(edge_ranges, edges, more_attrs...)
        kinds = Dict(map(i->(i=>K"block"), eachindex(edge_ranges)))
        sources = Dict(map(i->(i=>LineNumberNode(i)), eachindex(edge_ranges)))
        SyntaxGraph(
            edge_ranges,
            edges,
            Dict(:kind => kinds, :source => sources, more_attrs...))
    end

    @testset "unalias_nodes" begin
        # 1 -+-> 2 ->-> 4
        #    |      |
        #    +-> 3 -+
        g = testgraph([1:2, 3:3, 4:4, 0:-1], [2, 3, 4, 4], :foo => Dict(4=>"foo"))
        st = SyntaxTree(g, 1)
        stu = JuliaLowering.unalias_nodes(st)
        # Only node 4 should be copied, and no new edges are needed.
        @test stu._graph.edge_ranges == [1:2, 3:3, 4:4, 0:-1, 0:-1]
        @test stu._graph.edges == [2, 3, 4, 5]
        # Properties of node 4 should be preserved
        @test st[1][1].foo == stu[1][1].foo == stu[2][1].foo
        @test st[1][1].source == stu[1][1].source == stu[2][1].source
        # Try again with overlapping edge_ranges
        g = testgraph([1:2, 3:3, 3:3, 0:-1], [2, 3, 4], :foo => Dict(4=>"foo"))
        st = SyntaxTree(g, 1)
        stu = JuliaLowering.unalias_nodes(st)
        @test stu._graph.edge_ranges == [1:2, 3:3, 4:4, 0:-1, 0:-1]
        @test stu._graph.edges == [2, 3, 4, 5]
        @test st[1][1].foo == stu[1][1].foo == stu[2][1].foo
        @test st[1][1].source == stu[1][1].source == stu[2][1].source

        #           +-> 5
        #           |
        # 1 -+-> 2 -+---->>>-> 6
        #    |           |||
        #    +-> 3 -> 7 -+||
        #    |            ||
        #    +-> 4 -+-----+|
        #           |      |
        #           +------+
        g = testgraph([1:3, 4:5, 6:6, 7:8, 0:-1, 0:-1, 9:9],
                      [2, 3, 4, 5, 6, 7, 6, 6, 6],
                      :foo => Dict(6=>"foo"))
        st = SyntaxTree(g, 1)
        stu = JuliaLowering.unalias_nodes(st)
        # node 6 should be copied three times
        @test length(stu._graph.edge_ranges) == 10
        @test length(stu._graph.edges) == 9
        @test st[1][2].foo == stu[1][2].foo == stu[2][1][1].foo == stu[3][1].foo == stu[3][2].foo
        @test st[1][2].source == stu[1][2].source == stu[2][1][1].source == stu[3][1].source == stu[3][2].source

        # 1 -+-> 2 ->-> 4 -+----> 5 ->-> 7
        #    |      |      |         |
        #    +-> 3 -+      +-->-> 6 -+
        #        |            |
        #        +------------+
        g = testgraph([1:2, 3:3, 4:5, 6:7, 8:8, 9:9, 0:-1],
                      [2,3,4,4,6,5,6,7,7],
                      :foo => Dict(4=>4, 5=>5, 6=>6, 7=>7))
        st = SyntaxTree(g, 1)
        stu = JuliaLowering.unalias_nodes(st)
        @test length(stu._graph.edge_ranges) == 15
        @test length(stu._graph.edges) == 14
        # node 4
        @test st[1][1].foo == stu[1][1].foo == stu[2][1].foo
        # node 5
        @test st[1][1][1].foo == stu[1][1][1].foo == stu[2][1][1].foo
        # node 6
        @test st[1][1][2].foo == stu[1][1][2].foo == stu[2][1][2].foo == stu[2][2].foo
        # node 7
        @test st[1][1][1][1].foo == stu[1][1][1][1].foo == stu[1][1][2][1].foo ==
            stu[2][1][1][1].foo == stu[2][1][2][1].foo == stu[2][2][1].foo
    end

    @testset "annotate_parent" begin
        chk_parent(st, parent) = get(st, :parent, nothing) === parent &&
            all(c->chk_parent(c, st._id), children(st))
        # 1 -+-> 2 ->-> 4 --> 5
        #    |      |
        #    +-> 3 -+
        g = testgraph([1:2, 3:3, 4:4, 5:5, 0:-1], [2, 3, 4, 4, 5])
        st = JuliaLowering.annotate_parent!(SyntaxTree(g, 1))
        @test chk_parent(st, nothing)
        # NamedTuple-based attrs
        g = JuliaLowering.freeze_attrs(testgraph([1:2, 3:3, 4:4, 5:5, 0:-1], [2, 3, 4, 4, 5]))
        st = JuliaLowering.annotate_parent!(SyntaxTree(g, 1))
        @test chk_parent(st, nothing)
    end

    @testset "prune" begin
        # [1]-+-> 2         5 --> 6
        #     |
        #     +-> 3 --> 4   7
        g = testgraph([1:2, 0:-1, 3:3, 0:-1, 4:4, 0:-1, 0:-1], [2, 3, 4, 6])
        st = SyntaxTree(g, 1)
        stp = JuliaLowering.prune(st)
        @test length(syntax_graph(stp).edge_ranges) === 4
        @test numchildren(stp) === 2
        @test JuliaSyntax.is_leaf(stp[1])
        @test numchildren(stp[2]) === 1
        @test JuliaSyntax.is_leaf(stp[2][1])
        @test stp.source == LineNumberNode(1)
        @test stp[1].source == LineNumberNode(2)
        @test stp[2].source == LineNumberNode(3)
        @test stp[2][1].source == LineNumberNode(4)

        # (also checks that the last prune didn't destroy the graph)
        # 1 -+-> 2         5 --> 6
        #    |
        #    +-> 3 --> 4  [7]
        st = SyntaxTree(g, 7)
        stp = JuliaLowering.prune(st)
        @test length(syntax_graph(stp).edge_ranges) === 1
        @test JuliaSyntax.is_leaf(stp)
        @test stp.source == LineNumberNode(7)

        # 1 -+->[2]->-> 4
        #    |      |
        #    +-> 3 -+
        g = testgraph([1:2, 3:3, 4:4, 0:-1], [2, 3, 4, 4])
        st = SyntaxTree(g, 2)
        stp = JuliaLowering.prune(st)
        @test length(syntax_graph(stp).edge_ranges) === 2
        @test numchildren(stp) === 1
        @test JuliaSyntax.is_leaf(stp[1])
        @test stp.source == LineNumberNode(2)
        @test stp[1].source == LineNumberNode(4)

        #  9 -->[1]--> 5    src(1) = 2
        # 10 --> 2 --> 6    src(2) = 3
        # 11 --> 3 --> 7    src(3) = 4
        # 12 --> 4 --> 8    else src(i) = line(i)
        g = testgraph([1:1, 2:2, 3:3, 4:4, 0:-1, 0:-1, 0:-1, 0:-1, 5:5, 6:6, 7:7, 8:8],
                      [5, 6, 7, 8, 1, 2, 3, 4],
                      :source => Dict(
                          1=>2, 2=>3, 3=>4,
                          map(i->(i=>LineNumberNode(i)), 4:12)...))
        st = SyntaxTree(g, 1)
        stp = JuliaLowering.prune(st)
        # 1, 5, 4, 8 should remain
        @test length(syntax_graph(stp).edge_ranges) === 4
        @test numchildren(stp) === 1
        @test numchildren(stp[1]) === 0
        @test stp.source isa NodeId
        orig_4 = SyntaxTree(syntax_graph(stp), stp.source)
        @test orig_4.source === LineNumberNode(4)
        @test numchildren(orig_4) === 1
        @test orig_4[1].source === LineNumberNode(8)
        @test stp[1].source === LineNumberNode(5)

        # Try again with node 3 explicitly marked reachable
        stp = JuliaLowering.prune(st, keep=JuliaLowering.SyntaxList(g, NodeId[3, 4]))
        # 1, 5, 4, 8, and now 3, 7 as well
        @test length(syntax_graph(stp).edge_ranges) === 6
        @test numchildren(stp) === 1
        @test numchildren(stp[1]) === 0
        @test stp.source isa NodeId
        @test stp[1].source === LineNumberNode(5)

        orig_3 = SyntaxTree(syntax_graph(stp), stp.source)
        @test orig_3.source isa NodeId
        orig_4 = SyntaxTree(syntax_graph(stp), orig_3.source)
        @test orig_4.source === LineNumberNode(4)

        @test numchildren(orig_3) === 1
        @test numchildren(orig_4) === 1
        @test orig_3[1].source === LineNumberNode(7)
        @test orig_4[1].source === LineNumberNode(8)

        # Try again with no node provenance
        stp = JuliaLowering.prune(st, keep=nothing)
        @test length(syntax_graph(stp).edge_ranges) === 2
        @test numchildren(stp) === 1
        @test numchildren(stp[1]) === 0
        @test stp.source === LineNumberNode(4)
        @test stp[1].source === LineNumberNode(5)

        # "real world" test with lowered output---not many properties we can
        # check without fragile tests, but there are some.
        test_mod = Module()
        code = "begin; x1=1; x2=2; x3=3; x4=begin; 4; end; begin; end; end"
        st0 = parsestmt(SyntaxTree, code)
        st5 = JuliaLowering.lower(test_mod, st0)
        stp = JuliaLowering.prune(st5)
        @test length(syntax_graph(stp).edge_ranges) < length(syntax_graph(st5).edge_ranges)
        @test stp.source isa NodeId
        @test SyntaxTree(syntax_graph(stp), stp.source) ≈ st0
        @test sourcetext(stp) == code
        # try without preserving st0
        stp = JuliaLowering.prune(st5, keep=nothing)
        @test length(syntax_graph(stp).edge_ranges) < length(syntax_graph(st5).edge_ranges)
        @test stp.source isa SourceRef
        @test sourcetext(stp) == code
    end
end
