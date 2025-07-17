using JuliaLowering: expr_to_SyntaxTree

@testset "Expr -> SyntaxTree: literals" begin
    @test expr_to_SyntaxTree(123) ~ @ast_ 123::K"Integer"
    @test expr_to_SyntaxTree(123.45) ~ @ast_ 123.45::K"Float"
    @test expr_to_SyntaxTree(UInt8(12)) ~ @ast_ UInt8(12)::K"HexInt"
    @test expr_to_SyntaxTree(UInt16(1234)) ~ @ast_ UInt16(1234)::K"HexInt"
    @test expr_to_SyntaxTree(UInt32(0x12345678)) ~ @ast_ UInt32(0x12345678)::K"HexInt"
    @test expr_to_SyntaxTree(UInt64(0x123456789)) ~ @ast_ UInt64(0x123456789)::K"HexInt"
    @test expr_to_SyntaxTree(:(10000000000000000000000000000000000000000)) ~
        @ast_ 10000000000000000000000000000000000000000::K"Integer"
    @test expr_to_SyntaxTree(1.2345678901f0) ~ @ast_ 1.2345678901f0::K"Float32"
    @test expr_to_SyntaxTree(true) ~ @ast_ true::K"Bool"
    @test expr_to_SyntaxTree("hello") ~ @ast_ "hello"::K"String"
    @test expr_to_SyntaxTree('c') ~ @ast_ 'c'::K"Char"
    @test expr_to_SyntaxTree('α') ~ @ast_ 'α'::K"Char"
    @test expr_to_SyntaxTree(:asdf) ~ @ast_ "asdf"::K"Identifier"
    @test expr_to_SyntaxTree(:x_) ~ @ast_ "x_"::K"Identifier"
    @test expr_to_SyntaxTree(:__) ~ @ast_ "__"::K"Placeholder"
    @test expr_to_SyntaxTree([1,2]) ~ @ast_ [1,2]::K"Value"
    @test expr_to_SyntaxTree(QuoteNode(:x)) ~ @ast_ [K"inert" "x"::K"Identifier"]
end

@testset "Expr -> SyntaxTree: Call" begin
    @test expr_to_SyntaxTree(Expr(:call, :f)) ~ @ast_ [K"call"
        "f"::K"Identifier"
    ]

    @test expr_to_SyntaxTree(Expr(:call, :f, :x, :y)) ~ @ast_ [K"call"
        "f"::K"Identifier"
        "x"::K"Identifier"
        "y"::K"Identifier"
    ]

    @test expr_to_SyntaxTree(
        Expr(:call, :f, Expr(:parameters,
                             Expr(:kw, :a, 1),
                             Expr(:kw, :b, 2)), :x, :y)
    ) ~ @ast_ [K"call"
        "f"::K"Identifier"
        "x"::K"Identifier"
        "y"::K"Identifier"
        [K"parameters"
            [K"=" "a"::K"Identifier" 1::K"Integer"]
            [K"=" "b"::K"Identifier" 2::K"Integer"]
        ]
    ]
end

@testset "Expr -> SyntaxTree: Short form functions" begin
    @test expr_to_SyntaxTree(
        Expr(:(=), Expr(:call, :f), 1)
    ) ~ @ast_ [K"function"(syntax_flags=JuliaSyntax.SHORT_FORM_FUNCTION_FLAG)
        [K"call"
            "f"::K"Identifier"
        ]
        1::K"Integer"
    ]
    @test expr_to_SyntaxTree(
        Expr(:(=),
             Expr(:where, Expr(:(::), Expr(:call, :f, :x), :T), :T),
             1
        )
    ) ~ @ast_ [K"function"(syntax_flags=JuliaSyntax.SHORT_FORM_FUNCTION_FLAG)
        [K"where"
            [K"::"
                [K"call"
                    "f"::K"Identifier"
                    "x"::K"Identifier"
                ]
                "T"::K"Identifier"
            ]
            "T"::K"Identifier"
        ]
        1::K"Integer"
    ]
end

@testset "Expr -> SyntaxTree: Update operators" begin
    update_ops = split(raw"""
        +    -   *   /
        //   \   ^   ÷
        %    <<  >>  >>>
        |    &   ⊻  
    """)

    @testset "dotted $dotted" for dotted in [true, false]
        for op in update_ops
            flags = dotted ? JuliaSyntax.DOTOP_FLAG : JuliaSyntax.EMPTY_FLAGS
            # @info "" op
            # @info "" @macroexpand @ast_ [K"op="(syntax_flags=flags)
            #     "x"::K"Identifier"
            #     op::K"Identifier"
            #     "y"::K"Identifier"
            # ]
            # break
            opeq = "$op="
            if dotted
                opeq = ".$opeq"
            end
            @test expr_to_SyntaxTree(
                Expr(Symbol(opeq), :x, :y)
            ) ~ @ast_ [K"op="(syntax_flags=flags)
                "x"::K"Identifier"
                op::K"Identifier"
                "y"::K"Identifier"
            ]
        end
    end
end

