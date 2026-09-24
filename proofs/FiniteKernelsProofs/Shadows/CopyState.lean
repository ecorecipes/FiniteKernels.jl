import FiniteKernelsProofs.Finite.Laws

/-!
# SA-Pass shadow module: copying a state versus tensoring it with itself

Claim `fk.copy-state-pointmass`, from `comp_copy_eq_tensor_iff_isPointMass`.
-/

namespace FiniteKernelsProofs.Shadows.CopyState

open FiniteKernelsProofs.Finite FiniteKernelsProofs.Finite.Kernel

/-- `comp_copy_eq_tensor_iff_isPointMass`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (p : State X), Normalised p →
    (comp p (copy X) = comp (copy Unit) (tensor p p) ↔ IsPointMass p)

/-- "copying a state equals tensoring it with itself … for point masses": every point mass
does satisfy the equation. -/
abbrev Shadow1 : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (a : X),
    comp (pointMass a) (copy X) = comp (copy Unit) (tensor (pointMass a) (pointMass a))

/-- "… exactly for point masses": nothing else does. -/
abbrev Shadow2 : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (p : State X), Normalised p →
    comp p (copy X) = comp (copy Unit) (tensor p p) → IsPointMass p

theorem forward1 : Candidate → Shadow1 := by
  intro h X _ _ a
  exact (h X (pointMass a) (Normalised.pointMass a)).mpr ⟨a, fun _ => rfl⟩

theorem forward2 : Candidate → Shadow2 := by
  intro h X _ _ p hp heq
  exact (h X p hp).mp heq

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 X _ _ p hp
  refine ⟨h2 X p hp, ?_⟩
  intro hpm
  obtain ⟨a, rfl⟩ := (isPointMass_iff_exists_pointMass p).mp hpm
  exact h1 X a

end FiniteKernelsProofs.Shadows.CopyState
