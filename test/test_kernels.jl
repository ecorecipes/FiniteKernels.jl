@testset "kernels" begin
    A = FiniteAxis(:A, [:a0, :a1])
    B = FiniteAxis(:B, [:b0, :b1, :b2])
    C = FiniteAxis(:C, [:c0, :c1])
    X = FiniteSpace(A)
    Y = FiniteSpace(B)
    Z = FiniteSpace(C)
    I = FiniteSpace()
    rng = Random.Xoshiro(20260906)

    @testset "construction and shape errors" begin
        k = FiniteKernel(X, Y, [0.5 0.1; 0.3 0.2; 0.2 0.7])
        @test k.dom == X && k.codom == Y
        @test size(k.table) == (3, 2)
        @test eltype(k) == Float64
        @test_throws KernelShapeError FiniteKernel(X, Y, rand(2, 3))
        err = try
            FiniteKernel(X, Y, rand(2, 3))
        catch e
            e
        end
        msg = sprint(showerror, err)
        @test occursin("(3, 2)", msg) && occursin("(2, 3)", msg)
        @test_throws KernelShapeError FiniteKernel(X, Y, rand(3))
        # The table is copied, so later mutation of the input does not leak in.
        t = [0.5 0.1; 0.3 0.2; 0.2 0.7]
        k2 = FiniteKernel(X, Y, t)
        t[1, 1] = 99.0
        @test k2.table[1, 1] == 0.5
        # Structural equality and hashing.
        @test k == k2 && hash(k) == hash(k2)
        @test k ≈ FiniteKernel(X, Y, [0.5 0.1; 0.3 0.2; 0.2 0.7] .+ 1e-12)
        @test !(k ≈ FiniteKernel(Y, X, rand(rng, 2, 3); check=false))
    end

    @testset "normalisation" begin
        @test_throws KernelNormalizationError FiniteKernel(X, Y,
                                                           [0.5 0.1; 0.3 0.2; 0.2 0.8])
        err = try
            FiniteKernel(X, Y, [0.5 0.1; 0.3 0.2; 0.2 0.8])
        catch e
            e
        end
        @test occursin("not normalised", sprint(showerror, err))
        u = FiniteKernel(X, Y, [0.5 0.1; 0.3 0.2; 0.2 0.8]; check=false)
        @test !is_normalized(u)
        @test is_normalized(normalize(u))
        @test normalize(u).table[:, 2] ≈ [0.1, 0.2, 0.8] ./ 1.1
        @test is_normalized(u; atol=0.2)
        @test assert_normalized(normalize(u)) isa FiniteKernel
        @test_throws KernelNormalizationError assert_normalized(u)
        z = FiniteKernel(X, Y, zeros(3, 2); check=false)
        @test_throws ArgumentError normalize(z)
        err = try
            normalize(z)
        catch e
            e
        end
        @test occursin("at input index (1,) sums to zero", err.msg)
        @test occursin("cannot be rescaled", err.msg)
        # A state with zero mass names the (empty) input index.
        @test_throws ArgumentError normalize(state(X, [0.0, 0.0]; check=false))
        @test_throws ArgumentError normalize(FiniteKernel(Y, I, [1.0, 0.0, 1.0];
                                                          check=false))
        # Kernels into the unit: the table must be all ones.
        @test is_normalized(discard_kernel(Y))
        @test !is_normalized(FiniteKernel(Y, I, [1.0, 0.5, 1.0]; check=false))
        @test normalize(FiniteKernel(Y, I, [2.0, 0.5, 1.0]; check=false)) ≈
              discard_kernel(Y)
        # Unit to unit.
        @test is_normalized(identity_kernel(I)) && size(identity_kernel(I).table) == ()
    end

    @testset "nonnegativity and finite entries" begin
        # A table with negative entries is not a morphism of FinStoch even when
        # every column sums to one.
        neg = [1.5 -0.5; -0.5 1.5]
        N = FiniteSpace(:N, [:n0, :n1])
        @test_throws KernelEntryError FiniteKernel(N, N, neg)
        err = try
            FiniteKernel(N, N, neg; name=:Bad)
        catch e
            e
        end
        @test err isa KernelEntryError
        @test err.index == CartesianIndex(2, 1) && err.value == -0.5 && err.name == :Bad
        msg = sprint(showerror, err)
        @test occursin("KernelEntryError in Bad:", msg)
        @test occursin("is negative", msg) && occursin("index (2, 1)", msg)
        @test occursin("value -0.5", msg)
        u = FiniteKernel(N, N, neg; check=false)
        @test is_normalized(u)          # column sums alone do not see the sign
        @test !is_stochastic(u)
        @test_throws KernelEntryError assert_normalized(u)
        # Rounding below zero is tolerated up to -atol.
        eps_neg = [1.0 0.0; -1e-12 1.0]
        @test FiniteKernel(N, N, eps_neg) isa FiniteKernel
        @test is_stochastic(FiniteKernel(N, N, eps_neg))
        @test_throws KernelEntryError FiniteKernel(N, N, eps_neg; atol=1e-14)
        # NaN and Inf are rejected explicitly, not through the column sums.
        for bad in (NaN, Inf, -Inf)
            t = [1.0 0.0; 0.0 1.0]
            t[2, 1] = bad
            @test_throws KernelEntryError FiniteKernel(N, N, t)
            e = try
                FiniteKernel(N, N, t)
            catch e
                e
            end
            @test occursin("is not finite", sprint(showerror, e))
            @test !is_stochastic(FiniteKernel(N, N, t; check=false))
        end
        # cpt and state check entries too, and check=false skips the check.
        @test_throws KernelEntryError cpt(A, C, [1.5 -0.5; 0.2 0.8])
        @test_throws KernelEntryError state(X, [1.5, -0.5])
        @test cpt(A, C, [1.5 -0.5; 0.2 0.8]; check=false) isa FiniteKernel
        @test state(X, [1.5, -0.5]; check=false) isa FiniteKernel
        @test KernelEntryError("m", CartesianIndex(1), -1.0).name === nothing
        @test !occursin(" in ",
                        sprint(showerror, KernelEntryError("m", CartesianIndex(1), -1.0)))
        # is_stochastic is the conjunction of the two halves.
        @test is_stochastic(cpt(A, C, [0.9 0.1; 0.2 0.8]))
        @test !is_stochastic(FiniteKernel(X, Y, [0.5 0.1; 0.3 0.2; 0.2 0.8]; check=false))
        @test is_stochastic(FiniteKernel(X, Y, [0.333 0.1; 0.333 0.2; 0.333 0.7];
                                         check=false); atol=1e-3)
    end

    @testset "type parameters and inference" begin
        k = cpt(A, C, [0.9 0.1; 0.2 0.8])
        l = cpt(C, [0.4, 0.6])
        # SPEC section 10.2: the rank is a type parameter, so the table field is
        # concretely typed.
        @test k isa FiniteKernel{Float64,2}
        @test l isa FiniteKernel{Float64,1}
        @test isconcretetype(typeof(k))
        @test fieldtype(typeof(k), :table) == Array{Float64,2}
        @test eltype(k) == Float64 && eltype(typeof(k)) == Float64
        @test eltype(FiniteKernel{Rational{Int}}) == Rational{Int}
        # The bare name is still usable as a UnionAll in annotations.
        @test k isa FiniteKernel && Dict{Symbol,FiniteKernel}(:k => k)[:k] == k
        @test @inferred(probability(k, :c1, :a1)) == 0.8
        @test @inferred(kernel_matrix(k)) isa Matrix{Float64}
        # The rank of a result depends on the number of axes of the spaces, which
        # is runtime data, so only the element type can be inferred statically.
        KT = FiniteKernel{Float64,2}
        @test Base.infer_return_type(compose_kernel, Tuple{KT,KT}) <: FiniteKernel{Float64}
        @test Base.infer_return_type(tensor_kernel, Tuple{KT,KT}) <: FiniteKernel{Float64}
        @test Base.infer_return_type(kernel_matrix, Tuple{KT}) == Matrix{Float64}
        @test Base.infer_return_type(probability, Tuple{KT,Symbol,Symbol}) == Float64
    end

    @testset "element types other than Float64" begin
        half = 1 // 2
        r = cpt(A, C, [half half; 1//4 3//4])
        @test r isa FiniteKernel{Rational{Int},2}
        @test is_stochastic(r) && is_normalized(r)
        @test probability(r, :c0, :a1) === 1 // 4
        rr = compose_kernel(r, cpt(C, C, [1//1 0//1; 0//1 1//1]))
        @test rr isa FiniteKernel{Rational{Int},2} && rr == r
        @test tensor_kernel(r, r) isa FiniteKernel{Rational{Int},4}
        @test normalize(FiniteKernel(FiniteSpace(), Z, [1 // 4, 1 // 4]; check=false)) ==
              cpt(C, [half, half])
        @test kernel_matrix(r) == [half 1//4; half 3//4]
        @test occursin("1//4", sprint(show, MIME("text/plain"), r))
        @test sprint(show, r) == "FiniteKernel{Rational{Int64}}(A{a0,a1} → C{c0,c1})"
        @test_throws KernelEntryError cpt(A, C, [3//2 -1//2; 1//4 3//4])
        # Float32 tables keep their element type through the algebra.
        f32 = cpt(A, C, Float32[0.9 0.1; 0.2 0.8])
        @test f32 isa FiniteKernel{Float32,2}
        @test compose_kernel(f32, cpt(C, C, Float32[1 0; 0 1])) isa FiniteKernel{Float32,2}
        @test eltype(tensor_kernel(f32, f32)) == Float32
    end

    @testset "atol keyword and error names" begin
        @test DEFAULT_ATOL == 1e-8
        # Rows that sum to one within 1e-3 (Netica-style rounding) but not within 1e-8.
        t = [0.333 0.1; 0.333 0.2; 0.333 0.7]
        @test_throws KernelNormalizationError FiniteKernel(X, Y, t)
        k = FiniteKernel(X, Y, t; atol=1e-3)
        @test k isa FiniteKernel && !is_normalized(k) && is_normalized(k; atol=1e-3)
        @test assert_normalized(k; atol=1e-3) === k
        @test_throws KernelNormalizationError assert_normalized(k)
        @test cpt(A, C, [0.999 0.0; 0.2 0.8]; atol=1e-2) isa FiniteKernel
        @test_throws KernelNormalizationError cpt(A, C, [0.999 0.0; 0.2 0.8])
        @test state(X, [0.3, 0.699]; atol=1e-2) isa FiniteKernel
        @test_throws KernelNormalizationError state(X, [0.3, 0.699])
        # The default tolerance is unchanged.
        @test FiniteKernel(X, Y, [0.5 0.1; 0.3 0.2; 0.2 0.7] .+ 1e-9) isa FiniteKernel
        # Errors carry the tolerance, the deviation and an optional variable name.
        err = try
            cpt(A, C, [0.999 0.0; 0.2 0.8]; name=:Grass)
        catch e
            e
        end
        @test err isa KernelNormalizationError
        @test err.name == :Grass && err.atol == DEFAULT_ATOL && err.max_deviation ≈ 1e-3
        msg = sprint(showerror, err)
        @test occursin("in Grass", msg) && occursin("atol = 1.0e-8", msg)
        err = try
            assert_normalized(k; name=:K)
        catch e
            e
        end
        @test err.name == :K &&
              occursin("KernelNormalizationError in K:", sprint(showerror, err))
        @test KernelNormalizationError("m", 0.5, 1e-8).name === nothing
        @test !occursin(" in ", sprint(showerror, KernelNormalizationError("m", 0.5, 1e-8)))
        err = try
            cpt([A, B], C, rand(rng, 3, 2, 2); name=:Wet)
        catch e
            e
        end
        @test err isa KernelShapeError && err.name == :Wet
        @test err.expected == (2, 3, 2) && err.got == (3, 2, 2)
        @test occursin("KernelShapeError in Wet:", sprint(showerror, err))
        err = try
            state(X, [0.3, 0.3, 0.4]; name=:S)
        catch e
            e
        end
        @test err isa KernelShapeError && err.name == :S
        @test KernelShapeError("m", (1,), (2,)).name === nothing
        err = try
            FiniteKernel(X, Y, rand(2, 3); name=:F)
        catch e
            e
        end
        @test err isa KernelShapeError && err.name == :F
    end

    @testset "cpt layout and round trip" begin
        t = rand(rng, 2, 3, 2)
        t ./= sum(t; dims=3)
        k = cpt([A, B], C, t)
        @test k.dom == tensor_space(X, Y) && k.codom == Z
        @test size(k.table) == (2, 2, 3)
        for i in 1:2, j in 1:3, c in 1:2
            @test k.table[c, i, j] == t[i, j, c]
        end
        @test cpt(k) == t
        @test probability(k, :c1, (:a0, :b2)) == t[1, 3, 2]
        @test_throws KernelShapeError cpt([A, B], C, rand(rng, 3, 2, 2))
        @test_throws KernelNormalizationError cpt([A, B], C, rand(rng, 2, 3, 2))
        @test cpt([A, B], C, rand(rng, 2, 3, 2); check=false) isa FiniteKernel
        # Single parent and no parents.
        k1 = cpt(A, C, [0.9 0.1; 0.2 0.8])
        @test cpt([A], C, [0.9 0.1; 0.2 0.8]) == k1
        @test kernel_matrix(k1) == [0.9 0.2; 0.1 0.8]
        @test probability(k1, :c1, :a1) == 0.8
        k0 = cpt(C, [0.3, 0.7])
        @test k0 == state(Z, [0.3, 0.7])
        @test cpt(k0) == [0.3, 0.7]
        # cpt of a kernel with a two-axis codomain is refused.
        @test_throws KernelShapeError cpt(tensor_kernel(k1, k1))
    end

    @testset "states and special kernels" begin
        p = state(X, [0.3, 0.7])
        @test p.dom == I && p.codom == X && p.table == [0.3, 0.7]
        @test_throws KernelShapeError state(X, [0.3, 0.3, 0.4])
        @test_throws KernelNormalizationError state(X, [0.3, 0.3])
        q = state(tensor_space(X, Y), fill(1 / 6, 2, 3))
        @test size(q.table) == (2, 3)
        @test state(tensor_space(X, Y), fill(1 / 6, 6)) == q
        @test uniform(tensor_space(X, Y)) ≈ q
        @test point_mass(X, :a1).table == [0.0, 1.0]
        @test dirac(X, :a1) == point_mass(X, :a1)
        @test point_mass(tensor_space(X, Y), :a0, :b2).table == [0 0 1; 0 0 0]
        @test point_mass(tensor_space(X, Y), (:a0, :b2)) ==
              point_mass(tensor_space(X, Y), :a0, :b2)
        @test probability(point_mass(X, :a1), :a1) == 1.0
        @test probability(uniform(I), ()) == 1.0

        f = deterministic(Y, X, b -> b == :b0 ? :a0 : :a1)
        @test kernel_matrix(f) == [1 0 0; 0 1 1]
        g = deterministic(tensor_space(X, Y), tensor_space(Y, X), (a, b) -> (b, a))
        @test g ≈ swap_kernel(X, Y)
        @test is_normalized(f) && is_normalized(g)

        r = random_kernel(rng, tensor_space(X, Y), Z)
        @test is_normalized(r) && all(>(0), r.table)
        @test size(r.table) == (2, 2, 3)
        @test is_normalized(random_kernel(X, Y))
    end

    @testset "composition" begin
        k = random_kernel(rng, X, Y)
        l = random_kernel(rng, Y, Z)
        kl = compose_kernel(k, l)
        @test kl.dom == X && kl.codom == Z
        @test kernel_matrix(kl) ≈ kernel_matrix(l) * kernel_matrix(k)
        # `compose_kernel` is checked against a composite computed by hand rather
        # than against another implementation (SPEC section 10.3).
        a = cpt(A, B, [0.5 0.3 0.2; 0.1 0.6 0.3])
        b = cpt(B, C, [1.0 0.0; 0.5 0.5; 0.0 1.0])
        expected = [0.65 0.35; 0.4 0.6]
        @test cpt(compose_kernel(a, b)) ≈ expected
        @test kernel_matrix(compose_kernel(a, b)) ≈ [0.65 0.4; 0.35 0.6]
        # Composing more than two kernels folds from the left.
        @test compose_kernel(k, l, identity_kernel(Z)) ≈ kl
        @test is_normalized(kl)
        @test_throws SpaceMismatchError compose_kernel(l, k)
        @test occursin("compose", sprint(showerror, SpaceMismatchError(:compose, Y, X)))
        # Explicit sum formula from SPEC section 10.3.
        for z in labels(C), x in labels(A)
            @test probability(kl, z, x) ≈
                  sum(probability(l, z, y) * probability(k, y, x) for y in labels(B))
        end
        p = state(X, [0.25, 0.75])
        @test apply(k, p) ≈ compose_kernel(p, k)
        @test apply(k, p).table ≈ kernel_matrix(k) * [0.25, 0.75]
        @test_throws SpaceMismatchError apply(l, k)
    end

    @testset "tensor" begin
        k = random_kernel(rng, X, Y)
        l = random_kernel(rng, Z, X)
        kl = tensor_kernel(k, l)
        @test kl.dom == tensor_space(X, Z) && kl.codom == tensor_space(Y, X)
        @test size(kl.table) == (3, 2, 2, 2)
        # `tensor_kernel` is checked against a product computed by hand rather
        # than against another implementation (SPEC section 10.4).
        a = cpt(A, C, [0.9 0.1; 0.2 0.8])
        b = cpt(C, [0.25, 0.75])
        ab = tensor_kernel(a, b)
        @test size(ab.table) == (2, 2, 2)
        @test ab.table[:, :, 1] ≈ [0.9*0.25 0.9*0.75; 0.1*0.25 0.1*0.75]
        @test ab.table[:, :, 2] ≈ [0.2*0.25 0.2*0.75; 0.8*0.25 0.8*0.75]
        @test tensor_kernel(a, b, identity_kernel(FiniteSpace())).table ≈ ab.table
        @test is_normalized(kl)
        # SPEC section 10.4 formula, with axes (codK, codL, domK, domL).
        for y in labels(B), x2 in labels(A), x1 in labels(A), z in labels(C)
            @test probability(kl, (y, x2), (x1, z)) ≈
                  probability(k, y, x1) * probability(l, x2, z)
        end
        # Tensor with states and with the unit.
        p = state(X, [0.25, 0.75])
        q = state(Z, [0.4, 0.6])
        @test tensor_kernel(p, q).table ≈ [0.25, 0.75] * [0.4, 0.6]'
        @test tensor_kernel(k, identity_kernel(I)) ≈ k &&
              tensor_kernel(identity_kernel(I), k) ≈ k
    end

    @testset "marginal" begin
        k = random_kernel(rng, X, tensor_space(Y, Z))
        m1 = marginal(k, 1)
        @test m1.codom == Y && m1.dom == X
        @test m1.table ≈ dropdims(sum(k.table; dims=2); dims=2)
        @test marginal(k, :B) == m1
        @test marginal(k, [1, 2]) == k
        m21 = marginal(k, [2, 1])
        @test m21.codom == tensor_space(Z, Y)
        @test m21.table ≈ permutedims(k.table, (2, 1, 3))
        @test marginal(k, Int[]) ≈ discard_kernel(X)
        @test_throws ArgumentError marginal(k, 3)
        @test_throws ArgumentError marginal(k, [1, 1])
        @test_throws ArgumentError marginal(random_kernel(rng, X, tensor_space(Y, Y)), :B)
        # Marginalising a joint state: sum rule.
        joint = state(tensor_space(X, Y), [0.1 0.2 0.3; 0.05 0.15 0.2])
        @test marginal(joint, 1).table ≈ [0.6, 0.4]
        @test marginal(joint, 2).table ≈ [0.15, 0.35, 0.5]
    end

    @testset "show" begin
        k = cpt(A, C, [0.9 0.1; 0.2 0.8])
        @test sprint(show, k) == "FiniteKernel{Float64}(A{a0,a1} → C{c0,c1})"
        s = sprint(show, MIME("text/plain"), k)
        @test occursin("a0", s) && occursin("c1", s) && occursin("0.9", s)
        @test occursin("()", sprint(show, MIME("text/plain"), state(X, [0.3, 0.7])))
        big = uniform(FiniteSpace(:W, [Symbol(:w, i) for i in 1:500]))
        @test occursin("column-stochastic", sprint(show, MIME("text/plain"), big))
    end
end
