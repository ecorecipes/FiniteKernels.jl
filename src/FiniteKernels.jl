"""
    FiniteKernels

Finite state spaces and stochastic kernels (conditional probability tables): the
Catlab-free numerical base of the ecorecipes compositional Bayesian-network
ecosystem.

The package provides the objects and morphisms of the category **FinStoch**
without naming the category: [`FiniteAxis`](@ref) and [`FiniteSpace`](@ref) are
labelled finite products, [`FiniteKernel`](@ref) is a normalised conditional
probability table, and the wiring operations are
[`compose_kernel`](@ref), [`tensor_kernel`](@ref), [`identity_kernel`](@ref),
[`copy_kernel`](@ref), [`discard_kernel`](@ref) and [`swap_kernel`](@ref)
(SPEC section 3.2). `MarkovCategories.jl` sits on top and registers exactly these
functions as a Catlab `@instance` of its GATlab theory `ThMarkovCategory`, so
that they become `compose`, `otimes`, `id`, `mcopy`, `delete` and `braid`; this
package deliberately depends on nothing but `LinearAlgebra` and `Random`, so that
downstream packages that only need numbers do not pay for the category-theory
layer.

Axis convention (ADR 0002): a kernel `X → Y` stores its table with the **output
axes first, then the input axes**, `size(table) == (size(Y)..., size(X)...)`, and
is normalised over the output axes for every input index. User-facing conditional
probability tables use the parents-first / child-last layout; [`cpt`](@ref) is
the single documented conversion between the two.

The laws these operations satisfy are those of a Markov category in the sense of
[Fritz2020](@cite), whose copy-discard fragment is [ChoJacobs2019](@cite)'s CD
category; they are checked numerically in `test/test_laws.jl` and proved for the
finite model in `proofs/`.

Part of the ecorecipes compositional Bayesian-network ecosystem.
"""
module FiniteKernels

using LinearAlgebra: I
using Random: AbstractRNG, default_rng

import LinearAlgebra: normalize

# Spaces
export FiniteAxis, FiniteSpace, factors, labels, axis_names, state_index, joint_states,
       tensor_space
# Kernels
export DEFAULT_ATOL
export FiniteKernel, is_normalized, is_stochastic, normalize, assert_normalized,
       kernel_matrix, probability, cpt, state, point_mass, dirac, uniform, deterministic,
       random_kernel
# Composition and utilities (SPEC section 3.2 names)
export compose_kernel, tensor_kernel, identity_kernel, copy_kernel, discard_kernel,
       swap_kernel, marginal, apply
# Exceptions
export InvalidAxisError, KernelShapeError, KernelEntryError, KernelNormalizationError,
       SpaceMismatchError

include("spaces.jl")
include("kernels.jl")
include("composition.jl")
include("copy_discard.jl")
include("show.jl")

end # module
