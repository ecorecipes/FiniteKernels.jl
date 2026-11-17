# Endokernels as Markov chains through ResilienceCore (ADR 0029).
using ResilienceCore: ResilienceCore, MarkovKernel, linearise, stationary_distribution,
                      resilience, mixing_time
using LinearAlgebra: eigen

@testset "resilience of endokernels" begin
    tree = FiniteAxis(:tree, [:grey_birch, :blackgum, :red_maple, :beech])
    # Rows: the current occupant; columns: the species that replaces it.
    P = [0.05 0.36 0.50 0.09
         0.01 0.57 0.25 0.17
         0.00 0.14 0.55 0.31
         0.00 0.01 0.03 0.96]
    k = cpt([tree], tree, P)

    @testset "transpose to ResilienceCore's row convention" begin
        m = linearise(k)
        @test m isa MarkovKernel
        @test m.P ≈ P
        @test all(r -> isapprox(sum(r), 1; atol=1e-14), eachrow(m.P))
    end

    @testset "stationary distribution against the left eigenvector" begin
        F = eigen(permutedims(P))
        v = real.(F.vectors[:, argmin(abs.(F.values .- 1))])
        v ./= sum(v)
        s = stationary_distribution(k)
        @test s isa FiniteKernel
        @test s.dom == FiniteSpace()
        @test s.codom == FiniteSpace(tree)
        @test vec(s.table) ≈ v
        @test probability(s, :beech) ≈ v[4]
        @test vec(apply(k, s).table) ≈ vec(s.table) atol = 1e-12
    end

    @testset "metrics forward to the Markov kernel" begin
        m = linearise(k)
        @test resilience(k) == resilience(m)
        @test mixing_time(k) == mixing_time(m)
        @test mixing_time(k; ε=0.01) == mixing_time(m; ε=0.01)
        @test resilience(k) > 0
    end

    @testset "product spaces keep the joint-state order" begin
        rng = Xoshiro(29)
        X = tensor_space(FiniteSpace(FiniteAxis(:a, [:x, :y])),
                         FiniteSpace(FiniteAxis(:b, [:u, :v, :w])))
        q = random_kernel(rng, X, X)
        m = linearise(q)
        @test size(m.P) == (6, 6)
        states = joint_states(X)
        for (i, from) in enumerate(states), (j, to) in enumerate(states)
            @test m.P[i, j] ≈ q.table[state_index(X, to), state_index(X, from)]
        end
        s = stationary_distribution(q)
        @test s.codom == X
        @test vec(s.table) ≈ ResilienceCore.stationary_distribution(m)
    end

    @testset "a kernel between different spaces has no dynamics" begin
        Y = FiniteSpace(FiniteAxis(:light, [:sun, :shade]))
        f = cpt([tree], FiniteAxis(:light, [:sun, :shade]),
                [0.9 0.1; 0.6 0.4; 0.3 0.7; 0.1 0.9])
        @test f.codom == Y
        @test_throws SpaceMismatchError linearise(f)
        @test_throws SpaceMismatchError stationary_distribution(f)
        @test_throws SpaceMismatchError resilience(f)
        @test_throws SpaceMismatchError mixing_time(f)
        @test_throws SpaceMismatchError linearise(state(FiniteSpace(tree), fill(0.25, 4)))
        @test_throws FiniteKernelsError linearise(f)
    end

    @testset "normalisation within FiniteKernels' tolerance" begin
        δ = DEFAULT_ATOL / 10
        Q = copy(P)
        Q[1, 1] += δ                 # a row off by less than atol: FinStoch accepts it
        Q[4, 1] = -δ / 2             # and an entry negative by less than atol
        Q[4, 4] += δ / 2
        q = cpt([tree], tree, Q)
        m = linearise(q)
        @test all(≥(0), m.P)
        @test all(r -> isapprox(sum(r), 1; atol=1e-14), eachrow(m.P))
        bad = FiniteKernel(FiniteSpace(tree), FiniteSpace(tree), 2 .* permutedims(P);
                           check=false)
        @test_throws KernelNormalizationError linearise(bad)
        @test linearise(bad; atol=2.0) isa MarkovKernel
    end

    @testset "one function per name with both packages loaded" begin
        shared = intersect(Set(names(FiniteKernels)), Set(names(ResilienceCore)))
        @test all(n -> getfield(FiniteKernels, n) === getfield(ResilienceCore, n), shared)
        @test FiniteKernels.state === ResilienceCore.state
        @test state(FiniteSpace(tree), fill(0.25, 4)) isa FiniteKernel
    end
end
