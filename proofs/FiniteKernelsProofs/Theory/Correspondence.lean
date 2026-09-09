import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic
import Mathlib.CategoryTheory.MarkovCategory.Basic

/-!
# FiniteKernelsProofs.Theory.Correspondence

Dictionary between the GATlab theories used by `MarkovCategories.jl` (`src/theory.jl`) and
Mathlib's `CopyDiscardCategory` / `MarkovCategory`, with the theorem of the finite model
(`Finite/Kernel.lean`, `Finite/Laws.lean`) that instantiates each axiom.

This module spans two Julia packages: the finite model it instantiates the axioms in belongs to
`FiniteKernels.jl`, which holds these proofs, while the GATlab side of the dictionary now lives in
`MarkovCategories.jl` (its `src/theory.jl` and `src/finstoch_model.jl`); `FiniteKernels.jl` itself
carries no Catlab or GATlab dependency and names the same operations `compose_kernel`,
`tensor_kernel`, `identity_kernel`, `copy_kernel`, `discard_kernel` and `swap_kernel`.

`ThCopyDiscardCategory` is `MarkovCategories.jl`'s alias for Catlab's
`ThMonoidalCategoryWithDiagonals` (`Catlab/src/theories/Monoidal.jl`, "Cartesian category"
section); `ThMarkovCategory` adds one axiom, the naturality of `delete`.

### Comonoid structure

* Copy `mcopy(A) :: A → A ⊗ A` (`Δ`) is Mathlib's `ComonObj.comul` (`Δ[X]`) and the
  finite kernel `copy X`; delete is `ComonObj.counit` (`ε[X]`) and `discard X`.
* Coassociativity `Δ(A) ⋅ (Δ(A) ⊗ id(A)) == Δ(A) ⋅ (id(A) ⊗ Δ(A))` is
  `ComonObj.comul_assoc`, proved by `Kernel.copy_assoc`.
* The two counit laws are `ComonObj.counit_comul` and `ComonObj.comul_counit`, proved by
  `copy_discard_left` and `copy_discard_right` (with `_strict` variants).
* Cocommutativity `Δ(A) ⋅ σ(A,A) == Δ(A)` is `IsCommComonObj.comul_comm`, proved by `copy_swap`.

### Tensor coherence

* `Δ(A⊗B) == (Δ(A) ⊗ Δ(B)) ⋅ (id(A) ⊗ σ(A,B) ⊗ id(B))` is
  `CopyDiscardCategory.copy_tensor`, proved by `copy_prod`.
* `◊(A⊗B) == ◊(A) ⊗ ◊(B)` is `CopyDiscardCategory.discard_tensor`, proved by `discard_prod`.
* `Δ(munit()) == id(munit())` and `◊(munit()) == id(munit())` are
  `CopyDiscardCategory.copy_unit` and `CopyDiscardCategory.discard_unit`, proved by
  `copy_unit` and `discard_unit`.
* The inherited symmetric monoidal structure corresponds to `SymmetricCategory` and the
  laws `comp_tensor`, `tensor_assoc`, `tensor_unit_*`, `swap_swap`, `tensor_swap`, `hexagon`.

### The Markov axiom and the non-axiom

* `f ⋅ ◊(B) == ◊(A) ⊣ [f::(A → B)]` is `MarkovCategory.discard_natural`.
  In the finite model `comp_discard_eq_discard_iff` says it holds exactly when `Normalised`.
* Copy naturality `f ⋅ Δ(B) == Δ(A) ⋅ (f ⊗ f)` is **not an axiom**: it is the property
  `Deterministic f` (`IsComonHom f`), characterised by `comp_copy_eq_iff_isDeterministic`.

Catlab's tensor is strict, so the Mathlib associator, unitors and `tensorμ` are identities on the
Julia side; in the finite model they are the reindexing kernels `assoc`, `leftUnitor`, ...,
`tensorμ`. The generic consequences of these axioms (`discard_natural` as a theorem,
`deterministic_comp`, `deterministic_copy`, `state_discard`) are stated once for the abstract
Mathlib classes in the sibling `BayesianNetworks.jl` proof project's `Markov/Basic.lean` and
are not repeated here. The `example`s below only check that each Mathlib field has the type
the dictionary claims.
-/

namespace FiniteKernelsProofs.Theory

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section CopyDiscard

variable [CopyDiscardCategory C]

-- Commutative comonoid axioms of `ThMonoidalCategoryWithDiagonals`.
example (X : C) : Δ[X] ≫ (X ◁ Δ[X]) = Δ[X] ≫ (Δ[X] ▷ X) ≫ (α_ X X X).hom := comul_assoc X
example (X : C) : Δ[X] ≫ (ε[X] ▷ X) = (λ_ X).inv := counit_comul X
example (X : C) : Δ[X] ≫ (X ◁ ε[X]) = (ρ_ X).inv := comul_counit X
example (X : C) : Δ[X] ≫ (β_ X X).hom = Δ[X] := IsCommComonObj.comul_comm X

-- Coherence axioms.
-- (`Δ[X ⊗ Y]` must be read with the `CopyDiscardCategory.comonObj` instance, not the generic
-- tensor product of comonoids `Comon.instComonObjTensorObj`; the axiom says the two agree.)
example (X Y : C) :
    letI : ComonObj (X ⊗ Y) := CopyDiscardCategory.comonObj (X ⊗ Y)
    Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ tensorμ X X Y Y := copy_tensor X Y
example (X Y : C) :
    letI : ComonObj (X ⊗ Y) := CopyDiscardCategory.comonObj (X ⊗ Y)
    ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ C)).hom := discard_tensor X Y
example : Δ[𝟙_ C] = (λ_ (𝟙_ C)).inv := copy_unit
example : ε[𝟙_ C] = 𝟙 (𝟙_ C) := discard_unit

-- Copy naturality is not an axiom; it is the definition of `Deterministic`.
example {X Y : C} (f : X ⟶ Y) [Deterministic f] : f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f) :=
  Deterministic.copy_natural f

end CopyDiscard

section Markov

variable [MarkovCategory C]

-- The one axiom `ThMarkovCategory` adds.
example {X Y : C} (f : X ⟶ Y) : f ≫ ε[Y] = ε[X] := MarkovCategory.discard_natural f

end Markov

end FiniteKernelsProofs.Theory
