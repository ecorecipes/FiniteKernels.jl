import FiniteKernelsProofs.Finite.Kernel
import FiniteKernelsProofs.Finite.Laws

/-!
# SA-Pass shadow module: discard naturality iff normalised

Claim `fk.discard-natural`. The candidate is `comp_discard_eq_discard_iff` restated abstractly,
universally quantified over the kernel and its types, so that neither checker can be discharged
by citing the proved global theorem.
-/

namespace FiniteKernelsProofs.Shadows.DiscardNatural

open FiniteKernelsProofs.Finite FiniteKernelsProofs.Finite.Kernel

/-- `comp_discard_eq_discard_iff`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (X Y : Type) [Fintype Y] (k : Kernel X Y),
    comp k (discard Y) = discard X ↔ Normalised k

/-- "discard is natural … if a kernel is normalised": every normalised kernel satisfies the
Markov axiom. -/
abbrev Shadow1 : Prop :=
  ∀ (X Y : Type) [Fintype Y] (k : Kernel X Y),
    Normalised k → comp k (discard Y) = discard X

/-- "… and only if": a kernel satisfying the Markov axiom is normalised. Nothing weaker is
promised by "if and only if", and nothing stronger: no nonnegativity is claimed. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y : Type) [Fintype Y] (k : Kernel X Y),
    comp k (discard Y) = discard X → Normalised k

theorem forward1 : Candidate → Shadow1 := by
  intro h X Y _ k hk
  exact (h X Y k).mpr hk

theorem forward2 : Candidate → Shadow2 := by
  intro h X Y _ k hk
  exact (h X Y k).mp hk

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 X Y _ k
  exact ⟨h2 X Y k, h1 X Y k⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated, so a restatement that
drifts from the proved theorem stops compiling. -/
theorem anchor : Candidate := fun _ _ _ k =>
  FiniteKernelsProofs.Finite.Kernel.comp_discard_eq_discard_iff k

end FiniteKernelsProofs.Shadows.DiscardNatural
