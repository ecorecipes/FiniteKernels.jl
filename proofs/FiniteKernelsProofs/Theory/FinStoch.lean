import FiniteKernelsProofs.Finite.Laws
import Mathlib.CategoryTheory.MarkovCategory.Basic

/-!
# FiniteKernelsProofs.Theory.FinStoch

**FinStoch as a Mathlib Markov category** (SPEC §6, §10.3–§10.5).

Objects are finite types, morphisms are nonnegative normalised real kernels, and the tensor
is the Cartesian product of state types with the independent product of kernels. Empty
objects are permitted: there is no stochastic map from an inhabited type to an empty type,
but this is not an obstruction to the category or its Markov structure.

The associators, unitors and symmetry are deterministic reindexings. Their coherence proofs
reduce to equality of the underlying functions, not to additional axioms. In particular
copy is **not** assumed natural for arbitrary kernels.

This packages the equations in `Finite/Kernel.lean`; it does not prove a correspondence with
Julia floating-point arrays, and it does not make open Bayesian-network syntax a category.
-/

set_option autoImplicit false

namespace FiniteKernelsProofs

open CategoryTheory Finite

/-- Finite state types with decidable equality, including the empty type. -/
structure FinStoch where
  carrier : Type
  [fintype : Fintype carrier]
  [decEq : DecidableEq carrier]

attribute [instance] FinStoch.fintype FinStoch.decEq

namespace FinStoch

instance instCategory : Category FinStoch where
  Hom X Y := {k : Kernel X.carrier Y.carrier // Kernel.Stochastic k}
  id X := ⟨Kernel.idK X.carrier, Kernel.Stochastic.ofFun id⟩
  comp k l := ⟨Kernel.comp k.1 l.1, k.2.comp l.2⟩
  id_comp k := Subtype.ext (Kernel.idK_comp k.1)
  comp_id k := Subtype.ext (Kernel.comp_idK k.1)
  assoc k l m := Subtype.ext (Kernel.comp_assoc k.1 l.1 m.1)

variable {X Y Z : FinStoch}

/-- A function induces a stochastic, deterministic morphism. -/
def det (f : X.carrier → Y.carrier) : X ⟶ Y :=
  ⟨Kernel.ofFun f, Kernel.Stochastic.ofFun f⟩

/-- A state-space equivalence induces an isomorphism of stochastic kernels. -/
def isoOfEquiv (e : X.carrier ≃ Y.carrier) : X ≅ Y where
  hom := det e
  inv := det e.symm
  hom_inv_id := Subtype.ext (by
    change Kernel.comp (Kernel.ofFun e) (Kernel.ofFun e.symm) = Kernel.idK X.carrier
    rw [Kernel.ofFun_comp_ofFun]
    exact Kernel.ofFun_congr fun x => e.symm_apply_apply x)
  inv_hom_id := Subtype.ext (by
    change Kernel.comp (Kernel.ofFun e.symm) (Kernel.ofFun e) = Kernel.idK Y.carrier
    rw [Kernel.ofFun_comp_ofFun]
    exact Kernel.ofFun_congr fun y => e.apply_symm_apply y)

instance instMonoidalCategoryStruct : MonoidalCategoryStruct FinStoch where
  tensorObj X Y := ⟨X.carrier × Y.carrier⟩
  tensorUnit := ⟨Unit⟩
  tensorHom f g := ⟨Kernel.tensor f.1 g.1, f.2.tensor g.2⟩
  whiskerLeft X _ _ g :=
    ⟨Kernel.tensor (Kernel.idK X.carrier) g.1, (Kernel.Stochastic.ofFun id).tensor g.2⟩
  whiskerRight f Y :=
    ⟨Kernel.tensor f.1 (Kernel.idK Y.carrier), f.2.tensor (Kernel.Stochastic.ofFun id)⟩
  associator X Y Z := isoOfEquiv (Equiv.prodAssoc X.carrier Y.carrier Z.carrier)
  leftUnitor X := isoOfEquiv (Equiv.punitProd X.carrier)
  rightUnitor X := isoOfEquiv (Equiv.prodPUnit X.carrier)

open MonoidalCategory

instance instMonoidalCategory : MonoidalCategory FinStoch :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun _ _ => Subtype.ext Kernel.tensor_idK)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' =>
      Subtype.ext (Kernel.comp_tensor f.1 g.1 f'.1 g'.1))
    (associator_naturality := fun f g h => Subtype.ext (Kernel.tensor_assoc f.1 g.1 h.1))
    (leftUnitor_naturality := fun f => Subtype.ext (Kernel.tensor_unit_left f.1))
    (rightUnitor_naturality := fun f => Subtype.ext (Kernel.tensor_unit_right f.1))
    (pentagon := by
      intro W X Y Z
      apply Subtype.ext
      change Kernel.comp (Kernel.tensor (Kernel.ofFun _) (Kernel.idK _))
        (Kernel.comp (Kernel.ofFun _) (Kernel.tensor (Kernel.idK _) (Kernel.ofFun _))) =
          Kernel.comp (Kernel.ofFun _) (Kernel.ofFun _)
      simp only [Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
      rfl)
    (triangle := by
      intro X Y
      apply Subtype.ext
      change Kernel.comp (Kernel.ofFun _)
        (Kernel.tensor (Kernel.idK _) (Kernel.ofFun _)) =
          Kernel.tensor (Kernel.ofFun _) (Kernel.idK _)
      simp only [Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
      rfl)

instance instSymmetricCategory : SymmetricCategory FinStoch where
  braiding X Y := isoOfEquiv (Equiv.prodComm X.carrier Y.carrier)
  braiding_naturality_left := by
    intro X Y f Z
    apply Subtype.ext
    exact Kernel.tensor_swap f.1 (Kernel.idK _)
  braiding_naturality_right := by
    intro X Y Z f
    apply Subtype.ext
    exact Kernel.tensor_swap (Kernel.idK _) f.1
  hexagon_forward := by
    intro X Y Z
    apply Subtype.ext
    exact Kernel.hexagon
  hexagon_reverse := by
    intro X Y Z
    apply Subtype.ext
    change Kernel.comp (Kernel.ofFun _)
      (Kernel.comp (Kernel.ofFun _) (Kernel.ofFun _)) =
        Kernel.comp (Kernel.tensor (Kernel.idK _) (Kernel.ofFun _))
          (Kernel.comp (Kernel.ofFun _) (Kernel.tensor (Kernel.ofFun _) (Kernel.idK _)))
    simp only [Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
    rfl
  symmetry := by
    intro X Y
    apply Subtype.ext
    exact Kernel.swap_swap

instance instComonObj (X : FinStoch) : ComonObj X where
  counit := ⟨Kernel.discard X.carrier, Kernel.Nonneg.discard, Kernel.Normalised.discard⟩
  comul := det fun x => (x, x)
  counit_comul := Subtype.ext Kernel.copy_discard_left
  comul_counit := Subtype.ext Kernel.copy_discard_right
  comul_assoc := Subtype.ext (by
    change Kernel.comp (Kernel.copy X.carrier)
      (Kernel.tensor (Kernel.idK _) (Kernel.copy _)) =
        Kernel.comp (Kernel.copy X.carrier)
          (Kernel.comp (Kernel.tensor (Kernel.copy _) (Kernel.idK _)) (Kernel.assoc _ _ _))
    simpa only [Kernel.comp_assoc] using (Kernel.copy_assoc (X := X.carrier)))

instance instIsCommComonObj (X : FinStoch) : IsCommComonObj X where
  comul_comm := Subtype.ext Kernel.copy_swap

open scoped ComonObj

/-- The structural `tensorμ` of Mathlib is the middle-swap reindexing kernel. -/
theorem tensorμ_val (X Y : FinStoch) :
    (MonoidalCategory.tensorμ X X Y Y).val = Kernel.tensorμ X.carrier Y.carrier := by
  simp only [MonoidalCategory.tensorμ]
  change Kernel.comp (Kernel.ofFun _)
    (Kernel.comp (Kernel.tensor (Kernel.idK _) (Kernel.ofFun _))
      (Kernel.comp (Kernel.tensor (Kernel.idK _) (Kernel.tensor (Kernel.ofFun _) (Kernel.idK _)))
        (Kernel.comp (Kernel.tensor (Kernel.idK _) (Kernel.ofFun _)) (Kernel.ofFun _)))) = _
  simp only [Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun, Kernel.tensorμ]
  rfl

instance instMarkovCategory : MarkovCategory FinStoch where
  copy_tensor X Y := Subtype.ext (by
    change Kernel.copy (X.carrier × Y.carrier) =
      Kernel.comp (Kernel.tensor (Kernel.copy X.carrier) (Kernel.copy Y.carrier))
        (MonoidalCategory.tensorμ X X Y Y).val
    rw [tensorμ_val]
    exact Kernel.copy_prod)
  discard_tensor X Y := Subtype.ext Kernel.discard_prod
  copy_unit := Subtype.ext Kernel.copy_unit
  discard_unit := Subtype.ext Kernel.discard_unit
  discard_natural f := Subtype.ext (Kernel.Normalised.comp_discard f.2.2)

/-- The abstract Markov discard law uses exactly the normalisation carried by each hom. -/
theorem discard_natural (f : X ⟶ Y) : f ≫ ε[Y] = ε[X] :=
  MarkovCategory.discard_natural f

/-- Copy naturality still characterises deterministic kernels; it is not a Markov axiom. -/
theorem copy_natural_iff (f : X ⟶ Y) :
    f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f) ↔ Kernel.IsDeterministic f.val := by
  rw [Subtype.ext_iff]
  exact Kernel.comp_copy_eq_iff_isDeterministic f.1 f.2.2

/-- Empty objects are allowed, but normalisation rules out a map into one from a nonempty
object. No unmentioned inhabitance assumption is used by the category instances. -/
theorem no_hom_to_empty [Nonempty X.carrier] [IsEmpty Y.carrier] (f : X ⟶ Y) : False := by
  obtain ⟨x⟩ := ‹Nonempty X.carrier›
  have h := f.2.2 x
  simp at h

end FinStoch

end FiniteKernelsProofs
