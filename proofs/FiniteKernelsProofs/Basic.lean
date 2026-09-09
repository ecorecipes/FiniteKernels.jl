/-!
# FiniteKernelsProofs

Lean 4 / Mathlib formalisation accompanying `FiniteKernels.jl` (toolchain
`leanprover/lean4:v4.30.0`, Mathlib tag `v4.30.0`; ADR 0005). This document is generated from
the Lean sources by [mdgen](https://github.com/Seasawher/mdgen): the prose is the module
docstrings and the code blocks are the verbatim, machine-checked sources. Every library module
is built by `lake build --wfail`; `Audit.lean` prints the axioms of the headline results
(only `propext`, `Classical.choice`, `Quot.sound`). The Roadmap has no remaining proof holes.

## What is formalised

`FiniteKernels.jl` implements finite stochastic kernels (`FiniteKernel`, tables in the
outputs-first layout of ADR 0002), their sequential (`compose_kernel`) and parallel
(`tensor_kernel`) composition and copy/discard/swap operations. `MarkovCategories.jl`
exposes these as an instance of the GATlab theory `ThMarkovCategory` (SPEC §5–§6).
The exact kernel equations are proved pointwise and are now bundled into a Mathlib
`MarkovCategory FinStoch`, including the symmetric monoidal coherence laws. No external
`Stoch` development is vendored and no correspondence with floating-point code is asserted.

* `Finite/Kernel.lean`: the finite model `Kernel X Y := X → Y → ℝ`, its operations,
  preservation of normalisation/nonnegativity, and the category, symmetric-monoidal and
  commutative-comonoid laws.
* `Finite/Laws.lean`: discard naturality iff normalised; copy naturality iff deterministic;
  "copy once is not two samples" for states.
* `Theory/Correspondence.lean`: the GATlab/Mathlib/finite-kernel dictionary, with examples
  checking the type of each Mathlib field.
* `Theory/FinStoch.lean`: concrete Mathlib category, monoidal, symmetric, comonoid and Markov
  instances; abstract copy naturality iff the kernel is deterministic. Empty objects are
  permitted without assuming nonexistent maps into them.
* `Roadmap.lean`: compatibility import and remaining representation questions; no unproved
  declarations.

## Correspondence with the Julia API

| Julia (`FiniteKernels.jl`) | Lean |
|:--------------|:----------------|
| `FiniteKernel` table `table[y..., x...]`, `kernel_matrix(k)[y, x]` | `Kernel X Y`, entry `k x y = P(y ∣ x)` |
| `is_normalized(k)` | `Kernel.Normalised k` |
| `compose_kernel(k, l)` (diagrammatic order) | `Kernel.comp k l` |
| `tensor_kernel(k, l)` | `Kernel.tensor k l` |
| `identity_kernel`, `copy_kernel`, `discard_kernel`, `swap_kernel` | `idK X`, `copy X`, `discard X`, `swap X Y` |
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
