import FiniteKernelsProofs.Theory.FinStoch

/-!
# SA-Pass shadow module: FinStoch is a Markov category on the finite stochastic kernels

Claim `fk.finstoch-markov`, from the `FinStoch` instances and `FinStoch.discard_natural`.

The claim is about a construction, so every shadow holds by the definitions and the claim is
registered as weak (`independently_provable = true`): it pins what "on finite stochastic
kernels" and "Markov" mean -- the morphisms are exactly the stochastic kernels, and discard is
natural for every one of them -- without discriminating further.
-/

namespace FiniteKernelsProofs.Shadows.FinStochMarkov

open CategoryTheory FiniteKernelsProofs FiniteKernelsProofs.Finite
open scoped ComonObj

/-- The morphisms of `FinStoch` are exactly the stochastic kernels, and the Markov discard law
holds for every morphism. -/
abbrev Candidate : Prop :=
  (∀ (X Y : FinStoch) (k : Kernel X.carrier Y.carrier),
      Kernel.Stochastic k ↔ ∃ f : X ⟶ Y, f.val = k) ∧
    ∀ (X Y : FinStoch) (f : X ⟶ Y), f ≫ ε[Y] = ε[X]

/-- "on finite stochastic kernels": every stochastic kernel is a morphism. -/
abbrev Shadow1 : Prop :=
  ∀ (X Y : FinStoch) (k : Kernel X.carrier Y.carrier), Kernel.Stochastic k →
    ∃ f : X ⟶ Y, f.val = k

/-- and nothing else is: every morphism is a stochastic kernel. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y : FinStoch) (f : X ⟶ Y), Kernel.Stochastic f.val

/-- "Markov category": discarding after any morphism is discarding. -/
abbrev Shadow3 : Prop :=
  ∀ (X Y : FinStoch) (f : X ⟶ Y), f ≫ ε[Y] = ε[X]

theorem forward1 : Candidate → Shadow1 := fun h X Y k hk => (h.1 X Y k).1 hk

theorem forward2 : Candidate → Shadow2 := fun h X Y f => (h.1 X Y f.val).2 ⟨f, rfl⟩

theorem forward3 : Candidate → Shadow3 := fun h => h.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := by
  intro h1 h2 h3
  refine ⟨fun X Y k => ⟨h1 X Y k, ?_⟩, h3⟩
  rintro ⟨f, rfl⟩
  exact h2 X Y f

/-- SA-Pass anchor: the cited construction proves `Candidate` as stated, so a restatement that
drifts from the proved construction stops compiling. -/
theorem anchor : Candidate :=
  ⟨fun _ _ k => ⟨fun hk => ⟨⟨k, hk⟩, rfl⟩, fun ⟨f, hf⟩ => hf ▸ f.2⟩,
   fun _ _ f => FinStoch.discard_natural f⟩

end FiniteKernelsProofs.Shadows.FinStochMarkov
