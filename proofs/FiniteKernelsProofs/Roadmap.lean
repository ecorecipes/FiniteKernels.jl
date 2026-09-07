import FiniteKernelsProofs.Finite.Laws
import Mathlib.CategoryTheory.MarkovCategory.Basic

/-!
# Roadmap (contains `sorry`)

Module `FiniteKernelsProofs.Roadmap`.
Statements that are **not** part of the default build and are excluded from `Audit.lean`
(`make roadmap` builds this file on its own). Everything here that is `sorry`-free is a
candidate to move into the default target once it is useful to something downstream.

* `FinStoch` with its `Category` instance (stochastic kernels between finite types) is proved
  from `Finite/Kernel.lean` and is sorry-free.
* The `MonoidalCategory` and `MarkovCategory` instances are deferred (plan "Lean 4 layer":
  do not vendor the open Mathlib PR that adds `Stoch`; a `MarkovCategory` instance on finite
  types is only worth building when a downstream statement needs it). The ingredients are all
  in `Finite/Kernel.lean` (`comp_tensor`, `tensor_assoc`, `tensor_unit_*`, `hexagon`,
  `copy_assoc`, `copy_discard_*`, `copy_swap`, `copy_prod`, `discard_prod`, `copy_unit`,
  `discard_unit`, `Normalised.comp_discard`); what is missing is the bookkeeping of
  whiskerings, the pentagon and triangle identities, and the `Subtype` plumbing.
-/

namespace FiniteKernelsProofs.Roadmap

open CategoryTheory FiniteKernelsProofs.Finite

/-- Objects of **FinStoch**: finite types with decidable equality (`FiniteSpace`). -/
structure FinStoch where
  /-- The set of joint states. -/
  carrier : Type
  [fintype : Fintype carrier]
  [decEq : DecidableEq carrier]

attribute [instance] FinStoch.fintype FinStoch.decEq

/-- Morphisms are stochastic (nonnegative, normalised) kernels; composition is `compose`. -/
instance : Category FinStoch where
  Hom X Y := {k : Kernel X.carrier Y.carrier // Kernel.Stochastic k}
  id X := ⟨Kernel.idK X.carrier, Kernel.Stochastic.ofFun id⟩
  comp k l := ⟨Kernel.comp k.1 l.1, k.2.comp l.2⟩
  id_comp k := Subtype.ext (Kernel.idK_comp k.1)
  comp_id k := Subtype.ext (Kernel.comp_idK k.1)
  assoc k l m := Subtype.ext (Kernel.comp_assoc k.1 l.1 m.1)

/-- Deferred: the symmetric monoidal structure with `otimes` = `Kernel.tensor`. -/
noncomputable instance : MonoidalCategory FinStoch := sorry

/-- Deferred: the Markov structure with `mcopy` = `Kernel.copy`, `delete` = `Kernel.discard`;
`discard_natural` would be `Kernel.Normalised.comp_discard`. -/
noncomputable instance : MarkovCategory FinStoch := sorry

end FiniteKernelsProofs.Roadmap
