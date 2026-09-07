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

| GATlab (`ThMonoidalCategoryWithDiagonals`)                     | Mathlib                                   | Finite model (`Kernel.*`)          |
|--------------------------------------------|----------------------------------|----------------------------------------------|
| `mcopy(A) :: A → A ⊗ A`, `Δ`                                   | `ComonObj.comul`, `Δ[X]`                  | `copy X`                           |
| `delete(A) :: A → munit()`, `◊`                                | `ComonObj.counit`, `ε[X]`                 | `discard X`                        |
| `Δ(A) ⋅ (Δ(A) ⊗ id(A)) == Δ(A) ⋅ (id(A) ⊗ Δ(A))`               | `ComonObj.comul_assoc`                    | `copy_assoc`                       |
| `Δ(A) ⋅ (◊(A) ⊗ id(A)) == id(A)`                               | `ComonObj.counit_comul`                   | `copy_discard_left` (`_strict`)    |
| `Δ(A) ⋅ (id(A) ⊗ ◊(A)) == id(A)`                               | `ComonObj.comul_counit`                   | `copy_discard_right` (`_strict`)   |
| `Δ(A) ⋅ σ(A,A) == Δ(A)`                                        | `IsCommComonObj.comul_comm`               | `copy_swap`                        |
| `Δ(A⊗B) == (Δ(A) ⊗ Δ(B)) ⋅ (id(A) ⊗ σ(A,B) ⊗ id(B))`           | `CopyDiscardCategory.copy_tensor`         | `copy_prod`                        |
| `◊(A⊗B) == ◊(A) ⊗ ◊(B)`                                        | `CopyDiscardCategory.discard_tensor`      | `discard_prod`                     |
| `Δ(munit()) == id(munit())`                                    | `CopyDiscardCategory.copy_unit`           | `copy_unit`                        |
| `◊(munit()) == id(munit())`                                    | `CopyDiscardCategory.discard_unit`        | `discard_unit`                     |
| symmetric monoidal structure (`ThSymmetricMonoidalCategory`)   | `SymmetricCategory` (extended)            | `comp_tensor`, `tensor_assoc`, `tensor_unit_*`, `swap_swap`, `tensor_swap`, `hexagon` |

| GATlab (`ThMarkovCategory`)                                    | Mathlib                                   | Finite model                       |
|--------------------------------------------|----------------------------------|----------------------------------------------|
| `f ⋅ ◊(B) == ◊(A) ⊣ [f::(A → B)]`                              | `MarkovCategory.discard_natural`          | `comp_discard_eq_discard_iff` (holds iff `Normalised`) |
| *(not an axiom)* `f ⋅ Δ(B) == Δ(A) ⋅ (f ⊗ f)`                  | `Deterministic f` (= `IsComonHom f`)      | `comp_copy_eq_iff_isDeterministic` |

Catlab's tensor is strict, so the Mathlib associator, unitors and `tensorμ` are identities on the
Julia side; in the finite model they are the reindexing kernels `assoc`, `leftUnitor`, ...,
`tensorμ`. The generic consequences of these axioms (`discard_natural` as a theorem,
`deterministic_comp`, `deterministic_copy`, `state_discard`) are stated once for the abstract
Mathlib classes in `BayesianNetworks.jl/proofs/BayesianNetworksProofs/Markov/Basic.lean` and
are not repeated here. The `example`s below only check that each Mathlib field has the type
the table claims.
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
