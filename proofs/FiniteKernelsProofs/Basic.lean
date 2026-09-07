/-!
# FiniteKernelsProofs

Lean 4 / Mathlib formalisation accompanying `FiniteKernels.jl` (toolchain
`leanprover/lean4:v4.30.0`, Mathlib tag `v4.30.0`; ADR 0005). This document is generated from
the Lean sources by [mdgen](https://github.com/Seasawher/mdgen): the prose is the module
docstrings and the code blocks are the verbatim, machine-checked sources. Every declaration
outside the final "Roadmap" section is built by `lake build --wfail` and its axioms are printed
by `Audit.lean` (only `propext`, `Classical.choice`, `Quot.sound`).

## What is formalised

`FiniteKernels.jl` implements finite stochastic kernels (`FiniteKernel`, tables in the
outputs-first layout of ADR 0002), their sequential (`compose`) and parallel (`otimes`)
composition and the copy/discard/swap structure (`mcopy`, `delete`, `braid`) as an instance of
the GATlab theory `ThMarkovCategory` (SPEC §5–§6). The plan's "Lean 4 layer" asks for the laws
of that instance to be proved once, exactly, rather than only pinned numerically in
`test/test_laws.jl`, and for no Mathlib `MarkovCategory` instance to be built (the open Mathlib
`Stoch` pull request is not vendored). Accordingly the laws are stated pointwise about kernels.

| Part | Module | Content |
|:--|:-----------------|:-----------------------------------|
| 1 | `Finite/Kernel.lean` | The finite model `Kernel X Y := X → Y → ℝ` with `comp`, `tensor`, `idK`, `copy`, `discard`, `swap`, `pointMass`, `ofFun`; normalisation and nonnegativity are preserved; the category, symmetric-monoidal and commutative-comonoid laws. |
| 2 | `Finite/Laws.lean` | The characterisations the Julia tests pin: discard naturality iff normalised; copy naturality iff deterministic; "copy once is not two samples" for states. |
| 3 | `Theory/Correspondence.lean` | Dictionary GATlab `ThCopyDiscardCategory` / `ThMarkovCategory` ↔ Mathlib `CopyDiscardCategory` / `MarkovCategory` ↔ the finite model, with `example`s checking the type of each Mathlib field. |
| — | `Roadmap.lean` | `FinStoch` as a Mathlib `Category` (sorry-free) and the deferred monoidal / Markov instances (`sorry`); not in the default target. |

## Correspondence with the Julia API

| Julia (`FiniteKernels.jl`) | Lean |
|:--------------|:----------------|
| `FiniteKernel` table `table[y..., x...]`, `kernel_matrix(k)[y, x]` | `Kernel X Y`, entry `k x y = P(y ∣ x)` |
| `is_normalized(k)` | `Kernel.Normalised k` |
| `compose(k, l)` (diagrammatic order) | `Kernel.comp k l` |
| `otimes(k, l)` | `Kernel.tensor k l` |
| `id(X)`, `mcopy(X)`, `delete(X)`, `braid(X, Y)` | `idK X`, `copy X`, `discard X`, `swap X Y` |
| `deterministic(X, Y, f)`, `point_mass(X, a)`, `state(X, p)` | `ofFun f`, `pointMass a`, `State X` |
| testset "category laws" | `comp_assoc`, `idK_comp`, `comp_idK` |
| testset "monoidal laws" | `comp_tensor`, `tensor_idK`, `tensor_assoc`, `tensor_unit_left`, `tensor_unit_right`, `swap_swap`, `tensor_swap`, `hexagon` |
| testsets "comonoid laws", "coherence of copy and discard" | `copy_assoc`, `copy_discard_left`, `copy_discard_right`, `copy_swap`, `copy_prod`, `discard_prod`, `copy_unit`, `discard_unit` |
| "discard naturality iff normalised" | `comp_discard_eq_discard_iff` |
| "copy is natural for deterministic kernels only" | `comp_copy_eq_iff_isDeterministic` |
| "copy once is not two samples" (SPEC §6) | `comp_copy_eq_tensor_iff_isPointMass` |

SPEC §61's Propositions 1–7 concern Bayesian networks and influence diagrams and are
formalised in `BayesianNetworks.jl/proofs` and `InfluenceDiagrams.jl/proofs`; this project
supplies the kernel-level laws those build on. The generic consequences of the abstract axioms
(`discard_natural` as a theorem, `state_discard`, `deterministic_comp`, `deterministic_copy`)
are stated once, for Mathlib's classes, in `BayesianNetworksProofs.Markov.Basic`.
-/

namespace FiniteKernelsProofs

/-- Smoke lemma so that the axiom audit always has a first line. -/
theorem smoke : (1 : Nat) + 1 = 2 := rfl

end FiniteKernelsProofs
