# FiniteKernels.jl

Finite state spaces and stochastic kernels (conditional probability tables): the
Catlab-free numerical base of the ecorecipes Bayesian-network ecosystem
(`FiniteKernels` → `MarkovCategories` → `BayesianNetworks` →
`BayesianNetworkInference` → `InfluenceDiagrams`).

The package provides the objects and morphisms of the category **FinStoch**
without naming the category. [`FiniteAxis`](@ref) is one finite-valued variable,
[`FiniteSpace`](@ref) a labelled product of axes, and [`FiniteKernel`](@ref) a
normalised conditional probability table. The operations that wire kernels
together carry the SPEC section 3.2 names:

| operation | meaning |
|---|---|
| [`compose_kernel`](@ref) | feed the output of one kernel into the next |
| [`tensor_kernel`](@ref) | run two kernels side by side |
| [`identity_kernel`](@ref) | do nothing |
| [`copy_kernel`](@ref) | copy a value so several kernels can read it |
| [`discard_kernel`](@ref) | discard (marginalise out) a value |
| [`swap_kernel`](@ref) | swap the order of two wires |

They satisfy the laws of a Markov category [Fritz2020](@cite), whose
copy-discard fragment is the CD category of [ChoJacobs2019](@cite);
`test/test_laws.jl` checks them numerically on random kernels and `proofs/`
proves them in Lean for the finite model, including concrete Mathlib monoidal,
symmetric and Markov category instances. The former Roadmap holes are discharged;
the development remains an exact finite model, not a verification of the
floating-point array implementation. `MarkovCategories.jl` states those
laws as a GATlab theory and registers exactly these functions as a Catlab
`@instance`, so that they also answer to `compose`, `otimes`, `id`, `mcopy`,
`delete` and `braid`. This package depends on nothing but `LinearAlgebra` and
`Random`, so a package that only needs the numbers does not pay for the
category-theory layer.

## Quick start

```julia
using FiniteKernels

rain = FiniteAxis(:Rain, [:yes, :no])
grass = FiniteAxis(:Grass, [:wet, :dry])
R, G = FiniteSpace(rain), FiniteSpace(grass)

p = state(R, [0.2, 0.8])                          # I → Rain
k = cpt(rain, grass, [0.9 0.1; 0.2 0.8])          # Rain → Grass, parents-first layout

joint = compose_kernel(p, copy_kernel(R), tensor_kernel(identity_kernel(R), k))
marginal(joint, :Grass).table                     # [0.34, 0.66]

compose_kernel(p, copy_kernel(R)) ≈ tensor_kernel(p, p)   # false: copy once is not two samples
```

## Axis conventions

Two layouts are used deliberately, with exactly one documented conversion
between them (ADR 0002):

| layout | who uses it | shape | normalised over |
|---|---|---|---|
| user / IR | `cpt(parents, child, table)`, file formats, `BayesianNetworks.jl` | `(n(parents)..., n(child))` | the **last** axis |
| internal | `FiniteKernel.table` | `(size(codom)..., size(dom)...)` | the **output** (leading) axes |

`cpt(parents, child, table)` moves the child axis to the front with a single
`permutedims`; `cpt(kernel)` moves it back. `kernel_matrix(k)` is the
column-stochastic `length(codom) × length(dom)` matrix, so that
`compose_kernel(k, l)` is the matrix product `kernel_matrix(l) * kernel_matrix(k)`.
Joint states are enumerated in column-major order (first axis fastest), as
returned by [`joint_states`](@ref).

Composition is diagrammatic: `compose_kernel(k, l)` applies `k` first. The
tensor product `tensor_kernel(k, l)` has table axes
`(codom(k)..., codom(l)..., dom(k)..., dom(l)...)`.

## Errors

All failures are typed exceptions carrying the offending names, sizes or
entries: [`InvalidAxisError`](@ref), [`KernelShapeError`](@ref),
[`KernelEntryError`](@ref), [`KernelNormalizationError`](@ref) and
[`SpaceMismatchError`](@ref). All five subtype the abstract root
[`FiniteKernelsError`](@ref), so `e isa FiniteKernelsError` catches any of
them; invalid arguments, such as a zero column passed to [`normalize`](@ref),
raise Base's `ArgumentError` instead (ADR 0013).

A `FiniteKernel` built with the default `check=true` is a morphism of FinStoch:
its entries are finite and nonnegative (up to `-atol`) and each column sums to
one within `atol`. [`is_stochastic`](@ref) tests both halves; `check=false`
skips both (the shape is always checked).

See the Tutorials section for rendered vignettes and the API Reference for
docstrings.

## References

The package implements, in Julia, constructions from:

- [Fritz2020](@citet), which defines Markov categories and the naturality of
  discard that is exactly the normalisation condition on a kernel.
- [ChoJacobs2019](@citet), which defines the underlying copy-discard (CD)
  categories and the string-diagram calculus.
- [Fox1976](@citet), whose theorem identifies the categories in which copying is
  also natural as exactly the cartesian ones.
- [Mathlib2020](@citet), whose `CopyDiscardCategory`/`MarkovCategory` classes the
  Lean development in `proofs/` mirrors.

Full entries are on the [References](references.md) page.
