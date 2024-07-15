@testset "Syntax quoting & interpolation" begin

test_mod = Module()

ex = JuliaLowering.include_string(test_mod, """
begin
    x = 10
    y = :(g(z))
    quote
        f(\$(x+1), \$y)
    end
end
""")
@test ex ~ @ast_ [K"block"
    [K"call"
        "f"::K"Identifier"
        11::K"Value"
        [K"call"
            "g"::K"Identifier"
            "z"::K"Identifier"
        ]
    ]
]
@test sourcetext(ex[1]) == "f(\$(x+1), \$y)"
@test sourcetext(ex[1][2]) == "\$(x+1)"
@test sourcetext.(flattened_provenance(ex[1][3])) == ["\$y", "g(z)"]
@test sprint(io->showprov(io, ex[1][3], tree=true)) == raw"""
    (call g z)
    ├─ (call g z)
    │  └─ @ string:3
    └─ ($ y)
       └─ @ string:5
    """
@test sprint(io->showprov(io, ex[1][3])) == raw"""
    begin
        x = 10
        y = :(g(z))
    #         └──┘ ── in source
        quote
            f($(x+1), $y)
    # @ string:3

        y = :(g(z))
        quote
            f($(x+1), $y)
    #                 └┘ ── interpolated here
        end
    end
    # @ string:5"""


# Test expression flags are preserved during interpolation
@test JuliaSyntax.is_infix_op_call(JuliaLowering.include_string(test_mod, """
let
    x = 1
    :(\$x + \$x)
end
"""))

# interpolations at multiple depths
ex = JuliaLowering.include_string(test_mod, """
let
    args = (:(x),:(y))
    quote
        x = 1
        y = 2
        quote
            f(\$\$(args...))
        end
    end
end
""")
@test ex ~ @ast_ [K"block"
    [K"="
        "x"::K"Identifier"
        1::K"Integer"
    ]
    [K"="
        "y"::K"Identifier"
        2::K"Integer"
    ]
    [K"quote"
        [K"block"
            [K"call"
                "f"::K"Identifier"
                [K"$"
                    "x"::K"Identifier"
                    "y"::K"Identifier"
                ]
            ]
        ]
    ]
]
@test sourcetext(ex[3][1][1][2]) == "\$\$(args...)"
@test sourcetext(ex[3][1][1][2][1]) == "x"
@test sourcetext(ex[3][1][1][2][2]) == "y"

ex2 = JuliaLowering.eval(test_mod, ex)
@test sourcetext(ex2[1][2]) == "x"
@test sourcetext(ex2[1][3]) == "y"

@test JuliaLowering.include_string(test_mod, ":x") isa Symbol
@test JuliaLowering.include_string(test_mod, ":(x)") isa SyntaxTree

end