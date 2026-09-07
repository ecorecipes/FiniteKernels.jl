# SPEC section 55.1: the Markov-category laws hold numerically in FinStoch.
#
# The laws are stated with the SPEC section 3.2 names (`compose_kernel`,
# `tensor_kernel`, `identity_kernel`, `swap_kernel`, `copy_kernel`,
# `discard_kernel`), so that they are checked without the category-theory layer.
# `MarkovCategories.jl` binds Catlab's `compose`, `otimes`, `id`, `braid`,
# `mcopy` and `delete` to exactly these functions with an `@instance`.

# Random spaces with 1-3 axes of 2-3 states each.
function random_space(rng, name::Symbol; maxaxes::Int=3, maxstates::Int=3)
    n = rand(rng, 1:maxaxes)
    axes = [FiniteAxis(Symbol(name, i),
                       [Symbol(name, i, :_, j) for j in 1:rand(rng, 2:maxstates)])
            for i in 1:n]
    return FiniteSpace(axes)
end

@testset "laws" begin
    rng = Random.Xoshiro(1234)
    I = FiniteSpace()
    atol = 1e-12

    @testset "category laws" begin
        for trial in 1:10
            X, Y, Z, W = (random_space(rng, s) for s in (:x, :y, :z, :w))
            k = random_kernel(rng, X, Y)
            l = random_kernel(rng, Y, Z)
            m = random_kernel(rng, Z, W)
            @test compose_kernel(identity_kernel(X), k) ≈ k atol = atol
            @test compose_kernel(k, identity_kernel(Y)) ≈ k atol = atol
            @test compose_kernel(compose_kernel(k, l), m) ≈
                  compose_kernel(k, compose_kernel(l, m)) atol = atol
            @test compose_kernel(k, l).dom == X && compose_kernel(k, l).codom == Z
        end
    end

    @testset "monoidal laws" begin
        for trial in 1:10
            X, Y, Z = (random_space(rng, s) for s in (:x, :y, :z))
            X2, Y2, Z2 = (random_space(rng, s) for s in (:u, :v, :w))
            k, l, m = random_kernel(rng, X, X2), random_kernel(rng, Y, Y2),
                      random_kernel(rng, Z, Z2)
            # Associativity and unit of the tensor (strict on spaces).
            @test tensor_kernel(tensor_kernel(k, l), m) ≈
                  tensor_kernel(k, tensor_kernel(l, m)) atol = atol
            @test tensor_kernel(k, identity_kernel(I)) ≈ k atol = atol
            @test tensor_kernel(identity_kernel(I), k) ≈ k atol = atol
            @test tensor_kernel(identity_kernel(X), identity_kernel(Y)) ≈
                  identity_kernel(tensor_space(X, Y)) atol = atol
            # Interchange law.
            k2, l2 = random_kernel(rng, X2, Z), random_kernel(rng, Y2, Z2)
            @test compose_kernel(tensor_kernel(k, l), tensor_kernel(k2, l2)) ≈
                  tensor_kernel(compose_kernel(k, k2), compose_kernel(l, l2)) atol = atol
            # Symmetry: involutive, coherent and natural.
            @test compose_kernel(swap_kernel(X, Y), swap_kernel(Y, X)) ≈
                  identity_kernel(tensor_space(X, Y)) atol = atol
            @test swap_kernel(X, I) ≈ identity_kernel(X) atol = atol
            @test swap_kernel(I, X) ≈ identity_kernel(X) atol = atol
            @test swap_kernel(tensor_space(X, Y), Z) ≈
                  compose_kernel(tensor_kernel(identity_kernel(X), swap_kernel(Y, Z)),
                                 tensor_kernel(swap_kernel(X, Z), identity_kernel(Y))) atol = atol
            @test compose_kernel(tensor_kernel(k, l), swap_kernel(X2, Y2)) ≈
                  compose_kernel(swap_kernel(X, Y), tensor_kernel(l, k)) atol = atol
        end
    end

    @testset "comonoid laws" begin
        for trial in 1:10
            X = random_space(rng, :x)
            Δ, ε = copy_kernel(X), discard_kernel(X)
            @test Δ.dom == X && Δ.codom == tensor_space(X, X)
            @test ε.dom == X && ε.codom == I
            # Coassociativity.
            @test compose_kernel(Δ, tensor_kernel(Δ, identity_kernel(X))) ≈
                  compose_kernel(Δ, tensor_kernel(identity_kernel(X), Δ)) atol = atol
            # Counit laws.
            @test compose_kernel(Δ, tensor_kernel(ε, identity_kernel(X))) ≈
                  identity_kernel(X) atol = atol
            @test compose_kernel(Δ, tensor_kernel(identity_kernel(X), ε)) ≈
                  identity_kernel(X) atol = atol
            # Cocommutativity.
            @test compose_kernel(Δ, swap_kernel(X, X)) ≈ Δ atol = atol
        end
    end

    @testset "coherence of copy and discard with the tensor" begin
        for trial in 1:10
            # copy_kernel(X ⊗ Y) has length(X ⊗ Y)^3 entries, so keep these spaces small.
            X = random_space(rng, :x; maxaxes=2, maxstates=2)
            Y = random_space(rng, :y; maxaxes=2, maxstates=2)
            XY = tensor_space(X, Y)
            @test copy_kernel(XY) ≈
                  compose_kernel(tensor_kernel(copy_kernel(X), copy_kernel(Y)),
                                 tensor_kernel(tensor_kernel(identity_kernel(X),
                                                             swap_kernel(X, Y)),
                                               identity_kernel(Y))) atol = atol
            @test discard_kernel(XY) ≈
                  tensor_kernel(discard_kernel(X), discard_kernel(Y)) atol = atol
        end
        @test copy_kernel(I) ≈ identity_kernel(I)
        @test discard_kernel(I) ≈ identity_kernel(I)
    end

    @testset "discard naturality iff normalised" begin
        for trial in 1:10
            X, Y = random_space(rng, :x), random_space(rng, :y)
            k = random_kernel(rng, X, Y)
            @test compose_kernel(k, discard_kernel(Y)) ≈ discard_kernel(X) atol = atol
            # An unnormalised table violates the Markov axiom.
            u = FiniteKernel(X, Y, k.table .* (1 .+ rand(rng, size(k.table)...));
                             check=false)
            @test !is_normalized(u)
            @test !(compose_kernel(u, discard_kernel(Y)) ≈ discard_kernel(X))
            # The naturality equation is exactly the normalisation condition.
            for w in (k, u, normalize(u))
                @test is_normalized(w) ==
                      isapprox(compose_kernel(w, discard_kernel(w.codom)),
                               discard_kernel(w.dom); atol=1e-8)
            end
        end
        # A concrete counterexample: a column summing to 1.5.
        X = FiniteSpace(:X, [:a, :b])
        Y = FiniteSpace(:Y, [:u, :v])
        u = FiniteKernel(X, Y, [0.5 0.5; 1.0 0.5]; check=false)
        @test compose_kernel(u, discard_kernel(Y)).table == [1.5, 1.0]
        @test discard_kernel(X).table == [1.0, 1.0]
    end

    @testset "copy once is not two samples (SPEC section 6)" begin
        X = FiniteSpace(:X, [:a, :b, :c])
        p = state(X, [0.2, 0.3, 0.5])
        copied = compose_kernel(p, copy_kernel(X))   # draw once, then copy
        independent = tensor_kernel(p, p)            # draw independently twice
        @test copied.dom == independent.dom && copied.codom == independent.codom
        @test !(copied ≈ independent)
        @test copied.table ≈ [0.2 0 0; 0 0.3 0; 0 0 0.5]
        @test independent.table ≈ [0.2, 0.3, 0.5] * [0.2, 0.3, 0.5]'
        # Both marginals agree, so the difference is only in the correlation.
        @test marginal(copied, 1) ≈ marginal(independent, 1)
        @test marginal(copied, 2) ≈ marginal(independent, 2)
        # Equality holds exactly for point masses.
        for l in labels(factors(X)[1])
            q = point_mass(X, l)
            @test compose_kernel(q, copy_kernel(X)) ≈ tensor_kernel(q, q)
        end
        for trial in 1:20
            Z = random_space(rng, :z)
            probs = rand(rng, length(Z))
            probs ./= sum(probs)
            q = state(Z, probs)
            is_point = maximum(probs) ≈ 1
            @test isapprox(compose_kernel(q, copy_kernel(Z)), tensor_kernel(q, q);
                           atol=1e-8) == is_point
        end
        # More generally, copy is natural for deterministic kernels only.
        Y = FiniteSpace(:Y, [:u, :v])
        f = deterministic(X, Y, x -> x == :a ? :u : :v)
        @test compose_kernel(f, copy_kernel(Y)) ≈
              compose_kernel(copy_kernel(X), tensor_kernel(f, f))
        k = random_kernel(rng, X, Y)
        @test !(compose_kernel(k, copy_kernel(Y)) ≈
                compose_kernel(copy_kernel(X), tensor_kernel(k, k)))
    end
end
