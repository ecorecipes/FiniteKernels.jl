# The exception hierarchy of ADR 0013: every exception type this package defines, exported
# or not, subtypes the root `FiniteKernelsError`, and the types keep their module and their
# unqualified names.
function owned_exception_types(M)
    types = Type[]
    for n in names(M; all=true)
        isdefined(M, n) || continue
        T = getglobal(M, n)
        T isa Type && T <: Exception && parentmodule(T) === M && push!(types, T)
    end
    return types
end

@testset "errors" begin
    owned = owned_exception_types(FiniteKernels)

    @testset "hierarchy" begin
        @test isabstracttype(FiniteKernelsError)
        @test FiniteKernelsError <: Exception
        # The search is not vacuous: it finds the root and the five concrete types.
        @test issubset([FiniteKernelsError, InvalidAxisError, KernelShapeError,
                        KernelEntryError, KernelNormalizationError, SpaceMismatchError],
                       owned)
        for T in owned
            @test T <: FiniteKernelsError
            @test string(T) == string(nameof(T))
        end
    end

    @testset "construction errors are caught by the root" begin
        X = FiniteSpace(:X, [:a, :b])
        Y = FiniteSpace(:Y, [:u, :v, :w])
        @test_throws FiniteKernelsError FiniteAxis(:A, Symbol[])
        @test_throws FiniteKernelsError FiniteKernel(X, Y, rand(2, 3))
        @test_throws FiniteKernelsError FiniteKernel(FiniteSpace(), X, [1.5, -0.5])
        @test_throws FiniteKernelsError FiniteKernel(FiniteSpace(), X, [0.5, 0.6])
        @test_throws FiniteKernelsError compose_kernel(uniform(Y),
                                                       identity_kernel(X))
    end

    @testset "invalid arguments stay ArgumentError" begin
        X = FiniteSpace(:X, [:a, :b])
        zero_column = FiniteKernel(FiniteSpace(), X, [0.0, 0.0]; check=false)
        err = try
            normalize(zero_column)
        catch e
            e
        end
        @test err isa ArgumentError
        @test !(err isa FiniteKernelsError)
    end
end
