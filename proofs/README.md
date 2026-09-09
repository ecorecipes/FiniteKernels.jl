# FiniteKernelsProofs

Lean 4 / Mathlib formalisation for `FiniteKernels.jl` (toolchain v4.30.0, Mathlib v4.30.0; ADR 0005).

```sh
cd proofs
lake exe cache get   # prebuilt Mathlib oleans (once per Mathlib revision)
make build           # lake build --wfail: the default target, sorry-free
make audit           # #print axioms for every main theorem (Audit.lean)
make roadmap         # builds the compatibility/remaining-work module (no sorry)
```

The dependency checkout is shared with the other ecosystem `proofs/` projects via `packagesDir`
(`../../.lake-packages`). CI (`.github/workflows/lean.yml`) runs `lake build --wfail` and the audit;
`Roadmap.lean` is not imported by the default target and is not audited.

## Documents

The proofs are also rendered as a readable document (`FiniteKernelsProofs.md`, `.html`, `.pdf`, committed
here). It is generated from the Lean sources by [mdgen](https://github.com/Seasawher/mdgen)
(Lake dependency, tag `v4.30.0`): the `/-! ... -/` module docstrings become prose and everything
else becomes a `lean` code block, so the document is the verbatim, machine-checked source.

```sh
make mdgen   # FiniteKernelsProofs.md   — lake exe mdgen, modules concatenated in import order
make html    # FiniteKernelsProofs.html — pandoc --standalone --toc --mathjax, style.css
make pdf     # FiniteKernelsProofs.pdf  — pandoc → lualatex with header.tex (STIX Two Text/Math, JuliaMono)
make docs    # all three
```

Requirements: pandoc (≥ 3.8; `lean.xml` is a minimal Lean syntax definition, pandoc has none
built in) and a TeX distribution with `lualatex` (TinyTeX or MacTeX). Fonts: STIX Two Text and
STIX Two Math (macOS system fonts, or TeX Live `stix2-otf`) for prose and mathematics, and
[JuliaMono](https://juliamono.netlify.app) (SIL OFL) for code, which covers all of Lean's
Unicode; it is read from `../../fonts/JuliaMono/` by path (`header.tex`), not installed
system-wide. `make pdf` prints the number of `Missing character` warnings in the LaTeX log
(expected 0). The documents are built locally and committed; CI does not rebuild them.

Module order (`MD_FILES` in the `Makefile`, the import order of `FiniteKernelsProofs.lean`):

1. `Basic.lean` — introduction, structure and Julia-API correspondence tables
2. `Finite/Kernel.lean`
3. `Finite/Laws.lean`
4. `Theory/Correspondence.lean`
5. `Theory/FinStoch.lean`
6. `Roadmap.lean` — compatibility import and remaining questions; no unproved declarations

## What is formalised

`FiniteKernelsProofs/Finite/Kernel.lean` is the unbundled concrete finite model; its category
instances are in `Theory/FinStoch.lean`. `Kernel X Y := X → Y → ℝ` (the entry `k x y` is `P(y | x)`, i.e.
`table[y..., x...]` in the outputs-first layout of ADR 0002), the predicates `Normalised`
(`is_normalized`), `Nonneg` and `Stochastic`, and the operations `comp` (`compose`), `tensor`
(`otimes`), `idK` (`id`), `copy` (`mcopy`/`Δ`), `discard` (`delete`/`◊`), `swap` (`braid`/`σ`),
`pointMass` (`point_mass`), `ofFun` (`deterministic`). Because the tensor is strict in Julia but not
in Mathlib, the associator, unitors and `tensorμ` appear as explicit reindexing kernels
(`assoc`, `leftUnitor`, `rightUnitor`, `tensorμ`, `unitMul`).

Every structural morphism is `ofFun f` for a function `f`, and `ofFun` commutes with `comp` and
`tensor` (`ofFun_comp_ofFun`, `tensor_ofFun`, `comp_ofFun_left`, `comp_ofEquiv_right`); this
is what makes the monoidal and comonoid laws one-line proofs.

`FiniteKernelsProofs/Finite/Laws.lean` proves the characterisations the Julia tests pin numerically:

| Lean theorem | Statement | Julia test (`test/test_laws.jl`) |
|---|---|---|
| `comp_discard_eq_discard_iff` | `compose(k, delete(Y)) = delete(X)` iff `k` is normalised | "discard naturality iff normalised" |
| `comp_copy_eq_iff_isDeterministic` | for normalised `k`, `compose(k, mcopy(Y)) = compose(mcopy(X), otimes(k, k))` iff every column of `k` is a point mass | "copy is natural for deterministic kernels only" |
| `comp_copy_eq_tensor_iff_isPointMass` (and `'`, entrywise) | for a normalised state `p`, `compose(p, mcopy(X)) = otimes(p, p)` iff `p` is a point mass | "copy once is not two samples (SPEC section 6)" |
| `exists_pointMass_of_mul` | the arithmetic core: `q x * q x' = [x = x'] q x` and `∑ q = 1` force `q` to be an indicator | (the `maximum(probs) ≈ 1` check) |

Both directions of each `iff` are proved. The other Julia testsets map to `Kernel.lean` as follows:

| Julia testset | Lean theorems |
|---|---|
| "category laws" | `comp_assoc`, `idK_comp`, `comp_idK` |
| "monoidal laws" | `comp_tensor` (interchange), `tensor_idK`, `tensor_assoc`, `tensor_unit_left/right`, `swap_swap`, `tensor_swap` (naturality), `hexagon`, `swap_unit_right` |
| "comonoid laws" | `copy_assoc`, `copy_discard_left/right` (and `_strict`), `copy_swap` |
| "coherence of copy and discard with the tensor" | `copy_prod`, `discard_prod`, `copy_unit`, `discard_unit` |
| normalisation is preserved by the constructor checks | `Normalised.comp`, `Normalised.tensor`, `Normalised.ofFun/idK/copy/discard/swap/pointMass`, `Stochastic.comp/tensor` |

`FiniteKernelsProofs/Theory/Correspondence.lean` is a dictionary from the GATlab theory
(`ThCopyDiscardCategory = ThMonoidalCategoryWithDiagonals`, `ThMarkovCategory`;
`MarkovCategories.jl/src/theory.jl` and `test/test_theory.jl`) to the Mathlib fields (`ComonObj.comul_assoc`, `counit_comul`,
`comul_counit`, `IsCommComonObj.comul_comm`, `CopyDiscardCategory.copy_tensor`,
`discard_tensor`, `copy_unit`, `discard_unit`, `MarkovCategory.discard_natural`,
`Deterministic`) and to the theorems above, with `example`s checking the field types.

The generic consequences of the abstract axioms (`discard_natural` as a theorem, `state_discard`,
`deterministic_comp`, `deterministic_id`, `deterministic_copy`) are stated once for Mathlib's
`CopyDiscardCategory`/`MarkovCategory` in
`BayesianNetworks.jl/proofs/BayesianNetworksProofs/Markov/Basic.lean` and are not duplicated here.

## Concrete Mathlib instances

`Theory/FinStoch.lean` now bundles finite types into `FiniteKernelsProofs.FinStoch` and proves
the Mathlib `Category`, `MonoidalCategory`, `SymmetricCategory`, `ComonObj`,
`IsCommComonObj` and `MarkovCategory` instances. Tensor is exactly `Kernel.tensor`;
the unit is `Unit`; coherence maps are deterministic equivalences. The pentagon, triangle
and both hexagons reduce to equality of functions. `tensorμ_val` checks that Mathlib's
structural middle swap is the existing kernel operation.

Every instance is in the default build and audit. `copy_natural_iff` reuses the stochastic
hom's normalisation to prove that abstract copy naturality holds exactly for deterministic
kernels: no illicit naturality of copy has been assumed. Empty state types are allowed;
`no_hom_to_empty` proves why an inhabited type has no morphism into an empty one.

Both former Roadmap holes are discharged. `Roadmap.lean` only preserves the old object name
as an abbreviation. Still unproved: a bridge to Julia's named axes and floating-point arrays,
and an open-network syntax category or semantic functor. These are different claims.

## Design notes

* Entries are in `ℝ`, not `ℝ≥0`. None of the laws need nonnegativity (`Nonneg` is tracked
  separately and preserved), and the one real piece of arithmetic, `q * q = q ⟹ q ∈ {0, 1}` in
  `exists_pointMass_of_mul`, is a subtraction-and-`mul_eq_zero` argument that is awkward in the
  truncated-subtraction semiring `ℝ≥0`.
* Decidable equality is a class argument (`[DecidableEq X]`) rather than `Classical`, so the
  indicator kernels `ofFun` reduce definitionally and instance mismatches do not arise.
