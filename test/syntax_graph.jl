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

    nblocks(range) = Dict(map(i->(i=>K"block"), range))
    nlines(range) = Dict{NodeId, JuliaLowering.SourceAttrType}(
        map(i->(i=>LineNumberNode(i, "file")), range))

    @testset "unalias_nodes" begin
        # 1 -+-> 2 ->-> 4
        #    |      |
        #    +-> 3 -+
        g = SyntaxGraph([1:2, 3:3, 4:4, 0:-1], [2, 3, 4, 4],
                        Dict(:kind => nblocks(1:4), :source => nlines(1:4),
                             :foo => Dict(4=>"foo")))
        st = SyntaxTree(g, 1)
        stu = JuliaLowering.unalias_nodes(st)
        # Only node 4 should be copied, and no new edges are needed.
        @test stu._graph.edge_ranges == [1:2, 3:3, 4:4, 0:-1, 0:-1]
        @test stu._graph.edges == [2, 3, 4, 5]
        # Properties of node 4 should be preserved
        @test st[1][1].foo == stu[1][1].foo == stu[2][1].foo
        @test st[1][1].source == stu[1][1].source == stu[2][1].source
        # Try again with overlapping edge_ranges
        g = SyntaxGraph([1:2, 3:3, 3:3, 0:-1], [2, 3, 4],
                        Dict(:kind => nblocks(1:4), :source => nlines(1:4),
                             :foo => Dict(4=>"foo")))
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
        g = SyntaxGraph([1:3, 4:5, 6:6, 7:8, 0:-1, 0:-1, 9:9],
                        [2, 3, 4, 5, 6, 7, 6, 6, 6],
                        Dict(:kind => nblocks(1:7), :source => nlines(1:7),
                             :foo => Dict(6=>"foo")))
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
        g = SyntaxGraph([1:2, 3:3, 4:5, 6:7, 8:8, 9:9, 0:-1],
                        [2,3,4,4,6,5,6,7,7],
                        Dict(:kind => nblocks(1:7), :source => nlines(1:7),
                             :foo => Dict(4=>4, 5=>5, 6=>6, 7=>7)))
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
        g = SyntaxGraph([1:2, 3:3, 4:4, 5:5, 0:-1], [2, 3, 4, 4, 5],
                        Dict(:kind => nblocks(1:5), :source => nlines(1:5)))
        st = JuliaLowering.annotate_parent!(SyntaxTree(g, 1))
        @test chk_parent(st, nothing)
        # NamedTuple-based attrs
        g = SyntaxGraph([1:2, 3:3, 4:4, 5:5, 0:-1], [2, 3, 4, 4, 5],
                        (;kind=nblocks(1:5), source=nlines(1:5)))
        st = JuliaLowering.annotate_parent!(SyntaxTree(g, 1))
        @test chk_parent(st, nothing)
    end

    @testset "prune" begin
        test_mod = Module()
        st0 = parsestmt(SyntaxTree, "function foo end")
        st5 = JuliaLowering.lower(test_mod, st0)
        stp = JuliaLowering.prune(st5)
        # TODO
    end
end
