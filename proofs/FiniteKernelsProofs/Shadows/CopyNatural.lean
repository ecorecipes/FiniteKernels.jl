import FiniteKernelsProofs.Finite.Laws

/-!
# SA-Pass shadow module: copy naturality and determinism

Claim `fk.copy-natural-deterministic`, from `comp_copy_eq_iff_isDeterministic`.

The prose now reads "copying remains natural exactly for the deterministic normalised kernels",
which carries the same normalisation side condition as the Lean theorem. (An earlier revision
of the README dropped it; `Shadow2` was then unprovable, as it should have been -- the
"only if" half is false for an unnormalised kernel, e.g. `k = 0`.)
-/

namespace FiniteKernelsProofs.Shadows.CopyNatural

open FiniteKernelsProofs.Finite FiniteKernelsProofs.Finite.Kernel

/-- `comp_copy_eq_iff_isDeterministic`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (k : Kernel X Y), Normalised k →
    (comp k (copy Y) = comp (copy X) (tensor k k) ↔ IsDeterministic k)

/-- "copying remains natural … for deterministic kernels": determinism suffices. -/
abbrev Shadow1 : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (k : Kernel X Y),
    IsDeterministic k → comp k (copy Y) = comp (copy X) (tensor k k)

/-- "… exactly for the deterministic normalised kernels": among normalised kernels,
determinism is also necessary. This is what a reader of the sentence is entitled to conclude. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (k : Kernel X Y),
    Normalised k → comp k (copy Y) = comp (copy X) (tensor k k) → IsDeterministic k

theorem forward1 : Candidate → Shadow1 := by
  intro h X Y _ _ _ _ k hk
  exact (h X Y k hk.normalised).mpr hk

theorem forward2 : Candidate → Shadow2 := by
  intro h X Y _ _ _ _ k hk heq
  exact (h X Y k hk).mp heq

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 X Y _ _ _ _ k hk
  exact ⟨h2 X Y k hk, h1 X Y k⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated, so a restatement that
drifts from the proved theorem stops compiling. -/
theorem anchor : Candidate := fun _ _ _ _ _ _ k hk =>
  FiniteKernelsProofs.Finite.Kernel.comp_copy_eq_iff_isDeterministic k hk

end FiniteKernelsProofs.Shadows.CopyNatural
