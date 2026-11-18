# Resilience of Markov chains given as endokernels X → X, through ResilienceCore.jl
# (ADR 0029). The methods below extend ResilienceCore's functions; this package exports no
# new names for them, so `using FiniteKernels, ResilienceCore` gives one function per name.

# A kernel X → Y has dynamics only when Y == X: iterate it and the state stays on X.
function _endokernel(k::FiniteKernel, operation::Symbol)
    k.dom == k.codom || throw(SpaceMismatchError(operation, k.dom, k.codom))
    return k
end

"""
    ResilienceCore.linearise(k::FiniteKernel; atol=DEFAULT_ATOL) -> ResilienceCore.MarkovKernel

The Markov chain of an endokernel `k : X → X` as a `ResilienceCore.MarkovKernel`, whose
row-stochastic matrix `P` has `P[x, y] = P(y | x)`: the transpose of
[`kernel_matrix`](@ref)`(k)`, because this package stores kernels outputs first (ADR 0002)
and ResilienceCore stores Markov kernels row by row. States are numbered in
[`joint_states`](@ref) order of `X`, so on a product space the first axis varies fastest.

`k` must be a morphism of **FinStoch** within `atol` ([`assert_normalized`](@ref)); entries
that are negative by less than `atol` are set to zero and every row is then rescaled to sum
to exactly one, as ResilienceCore checks rows to a tolerance of `1e-10`. A kernel whose
domain and codomain differ has no dynamics and raises [`SpaceMismatchError`](@ref) (the
expected space is the domain, the one found is the codomain): compose it into a kernel
`X → X` first, for example with [`compose_kernel`](@ref).

The metrics `resilience`, `stationary_distribution` and `mixing_time` of ResilienceCore
also accept an endokernel directly.
"""
function ResilienceCore.linearise(k::FiniteKernel; atol::Real=DEFAULT_ATOL)
    _endokernel(k, :linearise)
    assert_normalized(k; atol)
    P = max.(permutedims(Float64.(kernel_matrix(k))), 0.0)
    P ./= sum(P; dims=2)
    return MarkovKernel(P)
end

"""
    ResilienceCore.stationary_distribution(k::FiniteKernel; atol=DEFAULT_ATOL) -> FiniteKernel

The stationary distribution of the Markov chain of an endokernel `k : X → X`, as a labelled
state `I → X` (see [`state`](@ref)) rather than a bare vector. It is ResilienceCore's
eigenvector of the transition matrix for eigenvalue one; for a chain with more than one
closed class it is one of several stationary distributions. Rounding below `atol` is
removed before the state is built.
"""
function ResilienceCore.stationary_distribution(k::FiniteKernel; atol::Real=DEFAULT_ATOL)
    π = ResilienceCore.stationary_distribution(ResilienceCore.linearise(k; atol))
    π = max.(π, 0.0)
    return state(k.codom, π ./ sum(π); atol)
end

"""
    ResilienceCore.resilience(k::FiniteKernel; atol=DEFAULT_ATOL)

The resilience of the Markov chain of an endokernel `k : X → X`: ResilienceCore's
`-log |λ₂|` of its transition matrix, the asymptotic rate per step at which a distribution
approaches the stationary one (`Inf` when `λ₂ = 0`).
"""
function ResilienceCore.resilience(k::FiniteKernel; atol::Real=DEFAULT_ATOL)
    return ResilienceCore.resilience(ResilienceCore.linearise(k; atol))
end

"""
    ResilienceCore.mixing_time(k::FiniteKernel; atol=DEFAULT_ATOL, ε=0.25, tmax=10^6)

The mixing time of the Markov chain of an endokernel `k : X → X`: ResilienceCore's first
step at which the distribution from every starting state is within total variation `ε` of
the stationary distribution, or `nothing` if that is not reached by `tmax` steps.
"""
function ResilienceCore.mixing_time(k::FiniteKernel; atol::Real=DEFAULT_ATOL, ε::Real=0.25,
                                    tmax::Integer=10^6)
    return ResilienceCore.mixing_time(ResilienceCore.linearise(k; atol); ε, tmax)
end
