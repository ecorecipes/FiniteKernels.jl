# FiniteKernels.jl

[![Build Status](https://github.com/ecorecipes/FiniteKernels.jl/actions/workflows/CI.yml/badge.svg)](https://github.com/ecorecipes/FiniteKernels.jl/actions/workflows/CI.yml)
[![Docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://ecorecipes.github.io/FiniteKernels.jl/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Finite state spaces and stochastic kernels (conditional probability tables): the Catlab-free numerical base of
the ecorecipes compositional Bayesian-network ecosystem.

Part of the ecorecipes compositional Bayesian-network ecosystem:
`FiniteKernels.jl` → `MarkovCategories.jl` → `BayesianNetworks.jl` → `BayesianNetworkInference.jl` →
`InfluenceDiagrams.jl`, with `BayesianNetworkFormats.jl` (file formats) and
`EcologicalBayesianNetworks.jl` (model zoo).

This package depends on `LinearAlgebra` and `Random` and nothing else. The category-theory layer — the GATlab
theory `ThMarkovCategory`, its free symbolic model and the Catlab `@instance` that turns the functions below
into `compose`, `otimes`, `id`, `mcopy`, `delete` and `braid` — lives in
[`MarkovCategories.jl`](https://github.com/ecorecipes/MarkovCategories.jl), one level up.

## Features

- `FiniteAxis` / `FiniteSpace`: labelled finite state spaces with a strictly associative tensor product
  (`tensor_space`) and a unit (`FiniteSpace()`).
- `FiniteKernel`: stochastic kernels (conditional probability tables) with a checked shape, checked finite
  nonnegative entries and checked normalisation, and typed errors (`KernelShapeError`, `KernelEntryError`,
  `KernelNormalizationError`, `SpaceMismatchError`, ...).
- One documented conversion, `cpt(parents, child, table)` / `cpt(kernel)`, between the user-facing
  parents-first / child-last layout and the internal outputs-first layout (ADR 0002).
- The wiring operations under their SPEC section 3.2 names: `compose_kernel`, `tensor_kernel`,
  `identity_kernel`, `copy_kernel`, `discard_kernel`, `swap_kernel`, plus `marginal`, `apply`,
  `kernel_matrix` and `probability`.
- A test suite checking every Markov-category law numerically, including that discard is natural if and only if
  a kernel is normalised, and that "copy once" differs from "sample twice" unless the state is a point mass.
- A Lean 4 / Mathlib development in [`proofs/`](proofs/) proving those laws for the finite model.

## Installation

The ecosystem packages are not registered. This package has no ecosystem dependencies, so install it
by URL on its own:

```julia
using Pkg
Pkg.add(url="https://github.com/ecorecipes/FiniteKernels.jl")
```

Requires Julia ≥ 1.12.

## Quick Start

```julia
using FiniteKernels

rain = FiniteAxis(:Rain, [:yes, :no])
grass = FiniteAxis(:Grass, [:wet, :dry])
R, G = FiniteSpace(rain), FiniteSpace(grass)

p = state(R, [0.2, 0.8])                          # I → Rain
k = cpt(rain, grass, [0.9 0.1; 0.2 0.8])          # Rain → Grass, table laid out (parent, child)

# I → Rain ⊗ Grass: draw the rain once, copy it, and feed one copy to the CPT.
joint = compose_kernel(p, copy_kernel(R), tensor_kernel(identity_kernel(R), k))
marginal(joint, :Grass).table                     # [0.34, 0.66]

compose_kernel(p, copy_kernel(R)) ≈ tensor_kernel(p, p)   # false: copy once is not two samples
compose_kernel(k, discard_kernel(G)) ≈ discard_kernel(R)  # true: discard is natural for normalised kernels
```

With `MarkovCategories.jl` loaded, the same wiring is written with Catlab's generic functions
(`compose(p, mcopy(R), otimes(id(R), k))`) and can be built symbolically first and interpreted afterwards.

Kernels store their tables with the output axes first (`size(k.table) == (size(codom)..., size(dom)...)`);
`cpt` is the single documented conversion from the parents-first layout used by file formats and the
network IR. See `docs/adr/0002-axis-convention.md`.

## Vignettes

Rendered vignettes live in [`vignettes/`](vignettes/) and are published in the
[documentation](https://ecorecipes.github.io/FiniteKernels.jl/).

## References

The package is an implementation of established constructions rather than new
theory; the works it most directly follows are:

- Fritz, T. (2020). A synthetic approach to Markov kernels, conditional independence and theorems on
  sufficient statistics. *Advances in Mathematics* 370, 107239.
  [doi:10.1016/j.aim.2020.107239](https://doi.org/10.1016/j.aim.2020.107239), arXiv:1908.07021.
- Cho, K. and Jacobs, B. (2019). Disintegration and Bayesian inversion via string diagrams.
  *Mathematical Structures in Computer Science* 29(7), 938-971.
  [doi:10.1017/S0960129518000488](https://doi.org/10.1017/S0960129518000488), arXiv:1709.00322.
- Fox, T. (1976). Coalgebras and cartesian categories. *Communications in Algebra* 4(7), 665-667.
  [doi:10.1080/00927877608822127](https://doi.org/10.1080/00927877608822127).
- The mathlib Community (2020). The Lean mathematical library. *CPP 2020*, 367-381.
  [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824).

The full bibliography for the ecosystem is `docs/src/references.bib` (also in
`vignettes/references.bib`); the rendered list is the References page of the
[documentation](https://ecorecipes.github.io/FiniteKernels.jl/).
