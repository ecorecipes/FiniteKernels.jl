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
state
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
depends on nothing but `LinearAlgebra` and `Random`.

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

## Exceptions

```@docs
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
