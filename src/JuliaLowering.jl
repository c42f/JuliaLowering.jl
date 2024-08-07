baremodule JuliaLowering

# ^ Use baremodule because we're implementing `Base.include` and `Core.eval`.
using Base
# We define a separate _include() for use in this module to avoid mixing method
# tables with the public `JuliaLowering.include()` API
_include(path::AbstractString) = Base.include(JuliaLowering, path)
using Core: eval

using JuliaSyntax

using JuliaSyntax: highlight, Kind, @KSet_str
using JuliaSyntax: is_leaf, children, numchildren, head, kind, flags, has_flags
using JuliaSyntax: filename, first_byte, last_byte, byte_range, sourcefile, source_location, span, sourcetext

using JuliaSyntax: is_literal, is_number, is_operator, is_prec_assignment, is_infix_op_call, is_postfix_op_call, is_error

_include("kinds.jl")
_register_kinds()

_include("syntax_graph.jl")
_include("ast.jl")
_include("utils.jl")

_include("macro_expansion.jl")
_include("desugaring.jl")
_include("scope_analysis.jl")
_include("linear_ir.jl")
_include("runtime.jl")

_include("eval.jl")

function __init__()
    _register_kinds()
end

end
