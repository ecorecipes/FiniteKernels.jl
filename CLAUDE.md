# FiniteKernels.jl

Finite state spaces and stochastic kernels (conditional probability tables): the Catlab-free numerical base of
the ecorecipes compositional Bayesian-network ecosystem.

## Place in the ecosystem

Dependency order (arrows = depends on):
EcologicalBayesianNetworks → InfluenceDiagrams → BayesianNetworkInference → BayesianNetworks →
FiniteKernels, and BayesianNetworks → BayesianNetworkFormats (a leaf).
MarkovCategories and CategoricalBayesianNetworks sit off that chain:
CategoricalBayesianNetworks → MarkovCategories → FiniteKernels, and
CategoricalBayesianNetworks → BayesianNetworks. Per ADR 0009 the model layer is free of
Catlab, which is a dependency of exactly those two packages; in particular
BayesianNetworks does **not** depend on MarkovCategories.
This package depends on one ecosystem package, ResilienceCore.jl (ADR 0029), fetched by URL through
`[sources]` together with its own dependency StructuredPopulationCore (Pkg does not follow a URL
dependency's sources). It has no ecosystem siblings on its path.

## Invariants that must not be broken

- **No Catlab and no GATlab, ever, in `[deps]`, `[extras]`, the docs or the vignette environment.** That is the
  point of the package (ADR 0001): the category-theory layer is `MarkovCategories.jl`, one level up. `Pkg.status`
  in this project must show neither. Julia dependencies are `LinearAlgebra`, `Random` and ResilienceCore (with
  StructuredPopulationCore), ADR 0029; ResilienceCore must stay free of Catlab and GATlab for this to hold.
- `state` is `ResilienceCore.state` extended with this package's methods (ADR 0029), so that loading both
  packages gives one name. Do not define a separate `state` function here.
- The wiring operations are named `compose_kernel`, `tensor_kernel`, `tensor_space`, `identity_kernel`,
  `copy_kernel`, `discard_kernel`, `swap_kernel` (SPEC section 3.2). Never define or import `compose`, `otimes`,
  `id`, `mcopy`, `delete`, `braid`, `dom` or `codom` here; `MarkovCategories.jl` binds those to these functions
  with a Catlab `@instance` and that is the only place it happens.
- Axis conventions: user-facing CPTs are `(parents..., child)` normalised over the last axis; FinStoch kernels
  internally are outputs-first, `size(table) == (size(codom)..., size(dom)...)`. `cpt(parents, child, table)` /
  `cpt(kernel)` is the only documented conversion (ADR 0002); never permute by hand.
- A `FiniteKernel` built with the default `check=true` is a morphism of FinStoch: finite entries, nonnegative up
  to `-atol`, columns summing to one within `atol` (`KernelEntryError` / `KernelNormalizationError`; ADR 0007).
  `check=false` skips both checks and nothing else; use it only where an unnormalised kernel is the point.
- `FiniteKernel{T,N}` keeps the rank in the type (SPEC 10.2). The rank of a composite is runtime data, so
  `compose_kernel`/`tensor_kernel` infer only the element type; keep `probability` and `kernel_matrix` inferable.
- Copying is not natural and must not become so: `compose_kernel(p, copy_kernel(X))` differs from
  `tensor_kernel(p, p)` unless `p` is a point mass, and discard is natural exactly for normalised kernels. Both
  directions are tested.

## Layout

- `src/spaces.jl`: `FiniteAxis`, `FiniteSpace`, `tensor_space`, `state_index`, `joint_states`.
- `src/errors.jl`: the root `FiniteKernelsError` and every exception under it (`InvalidAxisError`,
  `KernelShapeError`, `KernelEntryError`, `KernelNormalizationError`, `SpaceMismatchError`) with their `showerror`
  methods (ADR 0013). Included after `spaces.jl`, not first, because `SpaceMismatchError` has `FiniteSpace` fields.
- `src/kernels.jl`: `FiniteKernel{T,N}` (shape, entry and normalisation checks), `cpt`, `state`, `point_mass`,
  `uniform`, `deterministic`, `random_kernel`, `kernel_matrix`, `probability`, `is_stochastic`.
- `src/composition.jl`: `compose_kernel`, `tensor_kernel`, `identity_kernel`, `marginal`, `apply`.
- `src/copy_discard.jl`: `copy_kernel`, `discard_kernel`, `swap_kernel`.
- `src/show.jl`: printing.
- `src/resilience.jl`: an endokernel `X → X` as a Markov chain: methods of ResilienceCore's `linearise` (to a
  row-stochastic `MarkovKernel`, the transpose of `kernel_matrix`), `stationary_distribution` (a labelled state),
  `resilience` and `mixing_time`; `SpaceMismatchError` when the domain and codomain differ (ADR 0029). `test/test_{spaces,kernels,laws,errors,resilience,docstrings}.jl`: the suite, seeded RNGs only;
  `test_errors.jl` checks that every exception type the package defines subtypes `FiniteKernelsError`.
- `proofs/`: the Lean 4 / Mathlib library `FiniteKernelsProofs`, a finite model of the kernels and their laws.
  `Theory/FinStoch.lean` constructs the concrete monoidal, symmetric and Markov instances; the two former
  Roadmap holes are proved. No default or Roadmap target contains an unproved declaration. The instances
  do not verify Julia arrays or construct a category of open-network syntax. `Layout/` models the array
  layout exactly (values in any type, no Float64): column-major flat storage and its linear index (a bijection
  onto `Fin (∏ sizes)`; the 1-based `_linear_index` is it plus one), outputs-first kernel tables, `kernel_matrix`, the
  `(parents..., child)` CPT layout and the two `cpt` `permutedims` tuples (mutually inverse, entry-preserving),
  and `BayesianNetworkInference.multiply`'s result strides and odometer (the named product, for factors without
  repeated variables). It links index arithmetic, not Julia execution.

## Commands

```sh
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'   # the test suite
julia --project=docs docs/make.jl                                 # build docs locally
cd vignettes && quarto render                                     # render vignettes to html/gfm/pdf (julia engine; PDF needs lualatex + ../fonts/JuliaMono)
julia scripts/sync_vignettes.jl [--check]                         # copy vignettes into docs/src/tutorials
cd proofs && lake build --wfail && make audit                     # the Lean proofs and their axiom audit
```

## Files not to edit by hand

- `docs/src/tutorials/` is generated by `scripts/sync_vignettes.jl`.
- `vignettes/*/*.md`, `*.html`, `*.pdf` and `*_files/` are quarto output; edit the `.qmd`.
- `docs/adr/` is copied from the workspace `docs/adr/` by `scripts/sync_adrs.jl`; edit the workspace copy.
- `proofs/FiniteKernelsProofs.{md,html,pdf}` are generated by `make docs` in `proofs/`; edit the `.lean` sources.

## Style

JuliaFormatter `yas`; docstrings on every exported name, which `test/test_docstrings.jl` enforces; the docs
build is strict (no `warnonly`), so a docstring left out of the manual or a broken `@ref` fails it; typed
exceptions with variable names in the message, following ADR 0013: they live in `src/errors.jl` and subtype
the nearest root (`FiniteKernelsError`, `BayesianNetworkFormatsError` or `BayesNetError`), invalid arguments
and keywords raise `ArgumentError`, typed errors from a lower package pass through unchanged and documented, content read from a file, document or manifest is checked before it is converted and raises the package's typed error (ADR 0015: never catch the `MethodError` or `InexactError` of an unchecked conversion),
and another package's type is named as a code span, never with `@ref`; no emojis in code or docs.
