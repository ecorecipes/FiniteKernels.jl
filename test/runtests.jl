using Test
using FiniteKernels
using Random

@testset "FiniteKernels" begin
    include("test_spaces.jl")
    include("test_kernels.jl")
    include("test_laws.jl")
    include("test_docstrings.jl")
end
