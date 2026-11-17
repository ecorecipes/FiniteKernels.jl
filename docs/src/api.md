# API Reference

```@docs
FiniteKernels
```

## Spaces

```@docs
FiniteAxis
FiniteSpace
factors
labels
axis_names
Base.names(::FiniteSpace)
Base.size(::FiniteSpace)
Base.length(::FiniteSpace)
Base.ndims(::FiniteSpace)
tensor_space
state_index
joint_states
```

## Kernels

```@docs
FiniteKernel
cpt
state(::FiniteSpace, ::AbstractArray{<:Real})
point_mass
uniform
deterministic
random_kernel
DEFAULT_ATOL
is_normalized
is_stochastic
assert_normalized
normalize
kernel_matrix
probability
Base.isapprox(::FiniteKernel, ::FiniteKernel)
```

## Operations on kernels

The SPEC section 3.2 names of the wiring operations. `MarkovCategories.jl`
registers exactly these functions as a Catlab `@instance` of
`ThMarkovCategory`, which makes them available under the categorical names
`compose`, `otimes`, `id`, `braid`, `mcopy` and `delete` (with the operators
`⋅`, `⊗`, `σ`, `Δ`, `◊`); this package uses only the names below, so that it
depends on neither Catlab nor GATlab.

```@docs
compose_kernel
tensor_kernel
identity_kernel
copy_kernel
discard_kernel
swap_kernel
marginal
apply
```

## Markov chains and resilience

An endokernel `X → X` is a Markov chain. The functions below are ResilienceCore.jl's
(`using ResilienceCore`), with methods for a `FiniteKernel` (ADR 0029). This package
exports no new names for them, and its [`state`](@ref) extends ResilienceCore's `state`,
so loading both packages leaves no ambiguous name.

```@docs
ResilienceCore.linearise(::FiniteKernel)
ResilienceCore.stationary_distribution(::FiniteKernel)
ResilienceCore.resilience(::FiniteKernel)
ResilienceCore.mixing_time(::FiniteKernel)
```

## Exceptions

Every exception the package defines subtypes the abstract root
[`FiniteKernelsError`](@ref) (ADR 0013). Invalid arguments and keywords raise
Base's `ArgumentError`, which is outside it.

```@docs
FiniteKernelsError
InvalidAxisError
KernelShapeError
KernelEntryError
KernelNormalizationError
SpaceMismatchError
```

## Internal

```@docs
FiniteKernels.label_index
```
