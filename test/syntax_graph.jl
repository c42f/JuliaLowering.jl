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
        orig = Dict(map(i->(i=>i), eachindex(edge_ranges)))
        SyntaxGraph(
            edge_ranges,
            edges,
            Dict(:kind => kinds, :source => sources,
                 :orig => orig, more_attrs...))
    end

    @testset "copy_ast" begin
        # 1 --> 2 --> 3     src(7-9) = line 7-9
        # 4 --> 5 --> 6     src(i) = i + 3
        # 7 --> 8 --> 9
        g = testgraph([1:1, 2:2, 0:-1, 3:3, 4:4, 0:-1, 5:5, 6:6, 0:-1],
                      [2, 3, 5, 6, 8, 9],
                      :source => Dict(enumerate([
                          map(i->i+3, 1:6)...
                          map(LineNumberNode, 7:9)...])))
        st = SyntaxTree(g, 1)
        stcopy = JuliaLowering.copy_ast(g, st)
        # Each node should be copied once
        @test length(g.edge_ranges) === 18
        @test st._id != stcopy._id
        @test st ≈ stcopy
        @test st.source !== stcopy.source
        @test st.source[1] !== stcopy.source[1]
        @test st.source[1][1] !== stcopy.source[1][1]

        stcopy2 = JuliaLowering.copy_ast(g, st; copy_source=false)
        # Only nodes 1-3 should be copied
        @test length(g.edge_ranges) === 21
        @test st._id != stcopy2._id
        @test st ≈ stcopy2
        @test st.source === stcopy2.source
        @test st.source[1] === stcopy2.source[1]
        @test st.source[1][1] === stcopy2.source[1][1]

        # Copy into a new graph
        new_g = ensure_attributes!(SyntaxGraph(); JuliaLowering.attrdefs(g)...)
        stcopy3 = JuliaLowering.copy_ast(new_g, st)
        @test length(new_g.edge_ranges) === 9
        @test st ≈ stcopy3

        new_g = ensure_attributes!(SyntaxGraph(); JuliaLowering.attrdefs(g)...)
        # Disallow for now, since we can't prevent dangling sourcerefs
        @test_throws ErrorException JuliaLowering.copy_ast(new_g, st; copy_source=false)
    end

    @testset "unalias_nodes" begin
        # 1 -+-> 2 ->-> 4
        #    |      |
        #    +-> 3 -+
        g = testgraph([1:2, 3:3, 4:4, 0:-1], [2, 3, 4, 4])
        st = SyntaxTree(g, 1)
        stu = JuliaLowering.unalias_nodes(st)
        @test st ≈ stu
        @test length(stu._graph.edge_ranges) == 5
        @test length(stu._graph.edges) == 4
        # Properties of node 4 should be preserved
        @test 4 == stu[1][1].orig == stu[2][1].orig
        @test st[1][1].source == stu[1][1].source == stu[2][1].source
        @test stu[1][1]._id != stu[2][1]._id

        # Try again with overlapping edge_ranges
        g = testgraph([1:2, 3:3, 3:3, 0:-1], [2, 3, 4])
        st = SyntaxTree(g, 1)
        stu = JuliaLowering.unalias_nodes(st)
        @test st ≈ stu
        @test length(stu._graph.edge_ranges) == 5
        @test length(stu._graph.edges) == 4
        @test 4 == stu[1][1].orig == stu[2][1].orig
        @test st[1][1].source == stu[1][1].source == stu[2][1].source
        @test stu[1][1]._id != stu[2][1]._id

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
                      [2, 3, 4, 5, 6, 7, 6, 6, 6])
        st = SyntaxTree(g, 1)
        stu = JuliaLowering.unalias_nodes(st)
        @test st ≈ stu
        # node 6 should be copied three times
        @test length(stu._graph.edge_ranges) == 10
        @test length(stu._graph.edges) == 9
        # the four copies of node 6 should have attrs identical to the original and distinct ids
        @test 6 == stu[1][2].orig == stu[2][1][1].orig == stu[3][1].orig == stu[3][2].orig
        @test stu[1][2]._id != stu[2][1][1]._id != stu[3][1]._id != stu[3][2]._id

        # 1 -+-> 2 ->-> 4 -+----> 5 ->-> 7
        #    |      |      |         |
        #    +-> 3 -+      +-->-> 6 -+
        #        |            |
        #        +------------+
        g = testgraph([1:2, 3:3, 4:5, 6:7, 8:8, 9:9, 0:-1],
                      [2,3,4,4,6,5,6,7,7])
        st = SyntaxTree(g, 1)
        stu = JuliaLowering.unalias_nodes(st)
        @test st ≈ stu
        @test length(stu._graph.edge_ranges) == 15
        @test length(stu._graph.edges) == 14
        # attrs of nodes 4-7
        @test 4 == stu[1][1].orig == stu[2][1].orig
        @test 5 == stu[1][1][1].orig == stu[2][1][1].orig
        @test 6 == stu[1][1][2].orig == stu[2][1][2].orig == stu[2][2].orig
        @test 7 == stu[1][1][1][1].orig == stu[1][1][2][1].orig ==
            stu[2][1][1][1].orig == stu[2][1][2][1].orig == stu[2][2][1].orig
        # ensure no duplication
        @test stu[1][1][1][1]._id != stu[1][1][2][1]._id !=
            stu[2][1][1][1]._id != stu[2][1][2][1]._id != stu[2][2][1]._id
    end

    @testset "prune" begin
        # [1]-+-> 2         5 --> 6
        #     |
        #     +-> 3 --> 4   7
        g = testgraph([1:2, 0:-1, 3:3, 0:-1, 4:4, 0:-1, 0:-1], [2, 3, 4, 6])
        st = SyntaxTree(g, 1)
        stp = JuliaLowering.prune(st)
        @test st ≈ stp
        @test length(syntax_graph(stp).edge_ranges) === 4
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
        @test st ≈ stp
        @test length(syntax_graph(stp).edge_ranges) === 1
        @test stp.orig == 7

        # 1 -+->[2]->-> 4
        #    |      |
        #    +-> 3 -+
        g = testgraph([1:2, 3:3, 4:4, 0:-1], [2, 3, 4, 4])
        st = SyntaxTree(g, 2)
        stp = JuliaLowering.prune(st)
        @test st ≈ stp
        @test length(syntax_graph(stp).edge_ranges) === 2
        @test stp.orig == 2
        @test stp[1].orig == 4

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
        @test st ≈ stp
        # 1, 5, 4, 8 should remain
        @test length(syntax_graph(stp).edge_ranges) === 4
        @test stp.source isa NodeId
        orig_4 = SyntaxTree(syntax_graph(stp), stp.source)
        @test orig_4.source === LineNumberNode(4)
        @test numchildren(orig_4) === 1
        @test orig_4[1].source === LineNumberNode(8)
        @test stp[1].source === LineNumberNode(5)

        # Try again with node 3 explicitly marked reachable
        stp = JuliaLowering.prune(st, keep=JuliaLowering.SyntaxList(g, NodeId[3, 4]))
        @test st ≈ stp
        # 1, 5, 4, 8, and now 3, 7 as well
        @test length(syntax_graph(stp).edge_ranges) === 6
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
        @test st ≈ stp
        @test length(syntax_graph(stp).edge_ranges) === 2
        @test stp.source === LineNumberNode(4)
        @test stp[1].source === LineNumberNode(5)

        # "real world" test with lowered output---not many properties we can
        # check without fragile tests, but there are some.
        test_mod = Module()
        code = "begin; x1=1; x2=2; x3=3; x4=begin; 4; end; begin; end; end"
        st0 = parsestmt(SyntaxTree, code)
        st5 = JuliaLowering.lower(test_mod, st0)
        stp = JuliaLowering.prune(st5)
        @test st5 ≈ stp
        @test length(syntax_graph(stp).edge_ranges) < length(syntax_graph(st5).edge_ranges)
        @test stp.source isa NodeId
        @test SyntaxTree(syntax_graph(stp), stp.source) ≈ st0
        @test sourcetext(stp) == code
        # try without preserving st0
        stp = JuliaLowering.prune(st5, keep=nothing)
        @test st5 ≈ stp
        @test length(syntax_graph(stp).edge_ranges) < length(syntax_graph(st5).edge_ranges)
        @test stp.source isa SourceRef
        @test sourcetext(stp) == code
    end
end
