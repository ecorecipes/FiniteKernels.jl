@testset "spaces" begin
    @testset "FiniteAxis" begin
        a = FiniteAxis(:Rain, [:yes, :no])
        @test length(a) == 2
        @test labels(a) == [:yes, :no]
        @test a == FiniteAxis(:Rain, [:yes, :no])
        @test hash(a) == hash(FiniteAxis(:Rain, [:yes, :no]))
        @test a != FiniteAxis(:Rain, [:no, :yes])
        @test a != FiniteAxis(:Snow, [:yes, :no])
        @test_throws InvalidAxisError FiniteAxis(:Z, Symbol[])
        @test_throws InvalidAxisError FiniteAxis(:Z, [:a, :a])
        err = try
            FiniteAxis(:Z, [:a, :a])
        catch e
            e
        end
        msg = sprint(showerror, err)
        @test occursin(":Z", msg) && occursin("unique", msg)
        @test FiniteKernels.label_index(a, :no) == 2
        @test_throws InvalidAxisError FiniteKernels.label_index(a, :maybe)
        @test sprint(show, a) == "FiniteAxis(:Rain, [:yes, :no])"
    end

    @testset "FiniteSpace" begin
        X = FiniteSpace(:X, [:a, :b])
        Y = FiniteSpace([FiniteAxis(:Y, [:u, :v, :w])])
        @test factors(X) == [FiniteAxis(:X, [:a, :b])]
        @test size(X) == (2,)
        @test length(X) == 2
        @test ndims(X) == 1
        @test axis_names(X) == [:X]
        # `Base.names` is kept as a deprecated alias of `axis_names`.
        @test names(X) == axis_names(X)
        @test labels(X) == [[:a, :b]]
        @test X == FiniteSpace(:X, [:a, :b])
        @test hash(X) == hash(FiniteSpace(:X, [:a, :b]))
        @test X != Y

        I = FiniteSpace()
        @test isempty(I) && length(I) == 1 && size(I) == () && ndims(I) == 0

        XY = tensor_space(X, Y)
        @test factors(XY) == vcat(factors(X), factors(Y))
        @test size(XY) == (2, 3) && length(XY) == 6
        @test axis_names(XY) == [:X, :Y]
        @test names(XY) == axis_names(XY)
        @test axis_names(I) == Symbol[]
        @test tensor_space(tensor_space(X, Y), X) == tensor_space(X, tensor_space(Y, X))
        @test tensor_space(X, I) == X && tensor_space(I, X) == X
        @test tensor_space(X, X) ==
              FiniteSpace([FiniteAxis(:X, [:a, :b]), FiniteAxis(:X, [:a, :b])])
        @test tensor_space(X, Y, X) == tensor_space(XY, X)

        @test state_index(XY, :b, :w) == CartesianIndex(2, 3)
        @test state_index(XY, (:a, :u)) == CartesianIndex(1, 1)
        @test state_index(I) == CartesianIndex()
        @test_throws ArgumentError state_index(XY, :a)
        @test_throws InvalidAxisError state_index(XY, :a, :zzz)

        @test joint_states(XY) ==
              [(:a, :u), (:b, :u), (:a, :v), (:b, :v), (:a, :w), (:b, :w)]
        @test joint_states(I) == [()]

        @test sprint(show, XY) == "FiniteSpace(X{a,b} ⊗ Y{u,v,w})"
        @test sprint(show, I) == "FiniteSpace(I)"
    end
end
