import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# FiniteKernelsProofs.Finite.Kernel

A concrete finite model of the structure implemented by `FiniteKernels.jl`
(`src/kernels.jl`, `src/composition.jl`, `src/copy_discard.jl`): finite stochastic kernels
between finite types, with sequential composition, tensor product, copy, discard and swap.

No category instance is built here (ADR 0005, plan "Lean 4 layer"); the laws are stated
directly about kernels, pointwise, with the monoidal structure maps (associator, unitors,
`tensorμ`) written as *function-reindexing kernels* `ofFun e` for the obvious equivalences.

## Conventions

* `Kernel X Y := X → Y → ℝ`; `k x y` is the Julia entry `P(y | x)`, i.e. `table[y..., x...]`
  in the outputs-first layout of ADR 0002 (`kernel_matrix(k)[y, x]`).
* `Normalised k` is `is_normalized(k)`: every column `k x` sums to one.
* Entries live in `ℝ` rather than `ℝ≥0`; nonnegativity is the separate predicate `Nonneg`
  and is preserved by every construction, but none of the laws below need it.
* `comp k l` is the diagrammatic composite `compose(k, l)` (first `k`, then `l`), i.e. the
  matrix product `kernel_matrix(l) * kernel_matrix(k)`.
* `tensor k l` is `otimes(k, l)`, the outer product of the tables.
* Deterministic kernels are `ofFun f` (Julia `deterministic(X, Y, f)`); the identity, copy,
  discard, swap and point masses are all of this form, which is what makes the structural laws
  one-line proofs.
-/

namespace FiniteKernelsProofs.Finite

open Finset

/-- A finite kernel `X → Y` is a real-valued table `k x y = P(y | x)` (`FiniteKernel.table` in
the outputs-first layout, read as a function of the input first). -/
abbrev Kernel (X Y : Type) : Type := X → Y → ℝ

/-- A state `I → X` (`state(X, probs)`): a kernel out of the monoidal unit `Unit`. -/
abbrev State (X : Type) : Type := Kernel Unit X

namespace Kernel

variable {X Y Z W X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ : Type}

/-! ### Predicates -/

/-- `is_normalized(k)`: each column sums to one. -/
def Normalised [Fintype Y] (k : Kernel X Y) : Prop := ∀ x, ∑ y, k x y = 1

/-- All entries are nonnegative. -/
def Nonneg (k : Kernel X Y) : Prop := ∀ x y, 0 ≤ k x y

/-- A stochastic kernel: nonnegative and normalised (a morphism of **FinStoch**). -/
def Stochastic [Fintype Y] (k : Kernel X Y) : Prop := Nonneg k ∧ Normalised k

/-- A deterministic kernel in the sense of the Julia tests: every column is a point mass. -/
def IsDeterministic [DecidableEq Y] (k : Kernel X Y) : Prop :=
  ∀ x, ∃ y, ∀ y', k x y' = if y' = y then 1 else 0

/-- A state is a point mass (`point_mass(X, a)`) at some `a`. -/
def IsPointMass [DecidableEq X] (p : State X) : Prop :=
  ∃ a, ∀ x, p () x = if x = a then 1 else 0

/-! ### Constructions -/

/-- Sequential composition `compose(k, l)` (diagrammatic order): `(k ⋅ l)(z | x) = Σ_y k(y | x) l(z | y)`,
the matrix product `kernel_matrix(l) * kernel_matrix(k)`. -/
def comp [Fintype Y] (k : Kernel X Y) (l : Kernel Y Z) : Kernel X Z :=
  fun x z => ∑ y, k x y * l y z

/-- Parallel composition `otimes(k, l)`: the outer product `(k ⊗ l)(y₁, y₂ | x₁, x₂) = k(y₁ | x₁) l(y₂ | x₂)`. -/
def tensor (k : Kernel X₁ Y₁) (l : Kernel X₂ Y₂) : Kernel (X₁ × X₂) (Y₁ × Y₂) :=
  fun x y => k x.1 y.1 * l x.2 y.2

/-- The deterministic kernel `deterministic(X, Y, f)` induced by a function: `P(y | x) = [y = f x]`. -/
def ofFun [DecidableEq Y] (f : X → Y) : Kernel X Y :=
  fun x y => if y = f x then 1 else 0

/-- The identity kernel `id(X)` (`identity_kernel`). -/
def idK (X : Type) [DecidableEq X] : Kernel X X := ofFun id

/-- The copy map `mcopy(X) = Δ(X) : X → X ⊗ X`, `Δ(x₁, x₂ | x) = [x₁ = x][x₂ = x]` (`copy_kernel`). -/
def copy (X : Type) [DecidableEq X] : Kernel X (X × X) := ofFun fun x => (x, x)

/-- The discard map `delete(X) = ◊(X) : X → I`, the table of ones (`discard_kernel`). -/
def discard (X : Type) : Kernel X Unit := fun _ _ => 1

/-- The symmetry `braid(X, Y) = σ(X, Y) : X ⊗ Y → Y ⊗ X` (`swap_kernel`). -/
def swap (X Y : Type) [DecidableEq X] [DecidableEq Y] : Kernel (X × Y) (Y × X) :=
  ofFun (Equiv.prodComm X Y)

/-- The point mass `point_mass(X, a) = dirac(X, a) : I → X`. -/
def pointMass [DecidableEq X] (a : X) : State X := ofFun fun _ => a

/-- Push a state through a kernel (`apply(k, p) = compose(p, k)`). -/
def push [Fintype X] (k : Kernel X Y) (p : State X) : State Y := comp p k

/-! ### Structural reindexing kernels (the monoidal coherence data).

`FiniteKernels.jl` is strict (Julia tuples are flat), so these are all identities there;
Mathlib's `MonoidalCategory` is not strict, and its fields refer to them by name. -/

/-- The associator `α_ X Y Z : (X ⊗ Y) ⊗ Z → X ⊗ (Y ⊗ Z)` as a kernel. -/
def assoc (X Y Z : Type) [DecidableEq X] [DecidableEq Y] [DecidableEq Z] :
    Kernel ((X × Y) × Z) (X × (Y × Z)) := ofFun (Equiv.prodAssoc X Y Z)

/-- The left unitor `λ_ X : I ⊗ X → X` as a kernel. -/
def leftUnitor (X : Type) [DecidableEq X] : Kernel (Unit × X) X := ofFun (Equiv.punitProd X)

/-- The inverse left unitor `(λ_ X).inv : X → I ⊗ X` as a kernel. -/
def leftUnitorInv (X : Type) [DecidableEq X] : Kernel X (Unit × X) := ofFun (Equiv.punitProd X).symm

/-- The right unitor `ρ_ X : X ⊗ I → X` as a kernel. -/
def rightUnitor (X : Type) [DecidableEq X] : Kernel (X × Unit) X := ofFun (Equiv.prodPUnit X)

/-- The inverse right unitor `(ρ_ X).inv : X → X ⊗ I` as a kernel. -/
def rightUnitorInv (X : Type) [DecidableEq X] : Kernel X (X × Unit) := ofFun (Equiv.prodPUnit X).symm

/-- Mathlib's `tensorμ X X Y Y : (X ⊗ X) ⊗ (Y ⊗ Y) → (X ⊗ Y) ⊗ (X ⊗ Y)`, the middle swap
`id(X) ⊗ σ(X, Y) ⊗ id(Y)` of Catlab's coherence axiom for `mcopy`. -/
def tensorμ (X Y : Type) [DecidableEq X] [DecidableEq Y] :
    Kernel ((X × X) × (Y × Y)) ((X × Y) × (X × Y)) :=
  ofFun fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))

/-- The unique map `I ⊗ I → I` (`(λ_ I).hom`). -/
def unitMul : Kernel (Unit × Unit) Unit := ofFun fun _ => ()

/-! ### Pointwise evaluation lemmas -/

theorem ext_iff {k l : Kernel X Y} : k = l ↔ ∀ x y, k x y = l x y := by
  simp [funext_iff]

@[simp] theorem comp_apply [Fintype Y] (k : Kernel X Y) (l : Kernel Y Z) (x : X) (z : Z) :
    comp k l x z = ∑ y, k x y * l y z := rfl

@[simp] theorem tensor_apply (k : Kernel X₁ Y₁) (l : Kernel X₂ Y₂) (x : X₁ × X₂) (y : Y₁ × Y₂) :
    tensor k l x y = k x.1 y.1 * l x.2 y.2 := rfl

@[simp] theorem ofFun_apply [DecidableEq Y] (f : X → Y) (x : X) (y : Y) :
    ofFun f x y = if y = f x then 1 else 0 := rfl

@[simp] theorem discard_apply (x : X) (u : Unit) : discard X x u = 1 := rfl

theorem idK_apply [DecidableEq X] (x y : X) : idK X x y = if y = x then 1 else 0 := rfl

theorem copy_apply [DecidableEq X] (x x₁ x₂ : X) :
    copy X x (x₁, x₂) = if x₁ = x ∧ x₂ = x then 1 else 0 := by
  simp [copy, Prod.ext_iff]

theorem swap_apply [DecidableEq X] [DecidableEq Y] (x : X) (y : Y) (y' : Y) (x' : X) :
    swap X Y (x, y) (y', x') = if y' = y ∧ x' = x then 1 else 0 := by
  simp [swap, Prod.ext_iff]

theorem pointMass_apply [DecidableEq X] (a x : X) : pointMass a () x = if x = a then 1 else 0 := rfl

/-- `discard` is the deterministic kernel of the unique map to `Unit`. -/
theorem discard_eq_ofFun : discard X = ofFun fun _ => () := by
  funext x u; simp

/-! ### The deterministic-kernel calculus

Every structural morphism is `ofFun _`, and `ofFun` is a functor from functions to kernels
that is compatible with `tensor`. Together with the two lemmas for composing an arbitrary
kernel with `ofFun` on either side, these make the monoidal and comonoid laws mechanical. -/

/-- Precomposing with a deterministic kernel reindexes the input. -/
theorem comp_ofFun_left [Fintype Y] [DecidableEq Y] (f : X → Y) (l : Kernel Y Z) :
    comp (ofFun f) l = fun x z => l (f x) z := by
  funext x z
  simp [comp, ite_mul, Finset.sum_ite_eq']

/-- Postcomposing with the deterministic kernel of an equivalence reindexes the output. -/
theorem comp_ofEquiv_right [Fintype Y] [DecidableEq Z] (k : Kernel X Y) (e : Y ≃ Z) :
    comp k (ofFun e) = fun x z => k x (e.symm z) := by
  funext x z
  simp only [comp_apply, ofFun_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (e.symm z)]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb (e.symm_apply_eq.mpr h).symm
  · simp

/-- Postcomposing with a general deterministic kernel pushes mass forward. -/
theorem comp_ofFun_right [Fintype Y] [DecidableEq Z] (k : Kernel X Y) (g : Y → Z) :
    comp k (ofFun g) = fun x z => ∑ y, if z = g y then k x y else 0 := by
  funext x z
  simp [comp]

theorem ofFun_comp_ofFun [Fintype Y] [DecidableEq Y] [DecidableEq Z] (f : X → Y) (g : Y → Z) :
    comp (ofFun f) (ofFun g) = ofFun (g ∘ f) := by
  rw [comp_ofFun_left]; rfl

theorem tensor_ofFun [DecidableEq Y₁] [DecidableEq Y₂] (f : X₁ → Y₁) (g : X₂ → Y₂) :
    tensor (ofFun f) (ofFun g) = ofFun (Prod.map f g) := by
  funext x y
  rcases x with ⟨x₁, x₂⟩; rcases y with ⟨y₁, y₂⟩
  simp only [tensor_apply, ofFun_apply, Prod.map_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem ofFun_congr [DecidableEq Y] {f g : X → Y} (h : ∀ x, f x = g x) : ofFun f = ofFun g := by
  rw [funext h]

/-! ### Normalisation and nonnegativity are preserved -/

theorem Normalised.comp [Fintype Y] [Fintype Z] {k : Kernel X Y} {l : Kernel Y Z}
    (hk : Normalised k) (hl : Normalised l) : Normalised (comp k l) := by
  intro x
  have hl' : ∀ y, ∑ z, l y z = 1 := hl
  simp only [comp_apply]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, hl']
  exact hk x

theorem Normalised.tensor [Fintype Y₁] [Fintype Y₂] {k : Kernel X₁ Y₁} {l : Kernel X₂ Y₂}
    (hk : Normalised k) (hl : Normalised l) : Normalised (tensor k l) := by
  intro x
  simp only [tensor_apply]
  rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hk, hl, one_mul]

theorem Normalised.ofFun [Fintype Y] [DecidableEq Y] (f : X → Y) : Normalised (ofFun f) := by
  intro x
  simp [Finset.sum_ite_eq']

theorem Normalised.idK [Fintype X] [DecidableEq X] : Normalised (idK X) := Normalised.ofFun _
theorem Normalised.copy [Fintype X] [DecidableEq X] : Normalised (copy X) := Normalised.ofFun _
theorem Normalised.discard : Normalised (discard X) := by intro x; simp
theorem Normalised.swap [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    Normalised (swap X Y) := Normalised.ofFun _
theorem Normalised.pointMass [Fintype X] [DecidableEq X] (a : X) : Normalised (pointMass a) :=
  Normalised.ofFun _

theorem Nonneg.comp [Fintype Y] {k : Kernel X Y} {l : Kernel Y Z} (hk : Nonneg k) (hl : Nonneg l) :
    Nonneg (comp k l) := fun x z =>
  Finset.sum_nonneg fun y _ => mul_nonneg (hk x y) (hl y z)

theorem Nonneg.tensor {k : Kernel X₁ Y₁} {l : Kernel X₂ Y₂} (hk : Nonneg k) (hl : Nonneg l) :
    Nonneg (tensor k l) := fun _ _ => mul_nonneg (hk _ _) (hl _ _)

theorem Nonneg.ofFun [DecidableEq Y] (f : X → Y) : Nonneg (ofFun f) := by
  intro _ _; simp only [ofFun_apply]; split_ifs <;> norm_num

theorem Nonneg.discard : Nonneg (discard X) := fun _ _ => zero_le_one

theorem Stochastic.comp [Fintype Y] [Fintype Z] {k : Kernel X Y} {l : Kernel Y Z}
    (hk : Stochastic k) (hl : Stochastic l) : Stochastic (comp k l) :=
  ⟨hk.1.comp hl.1, hk.2.comp hl.2⟩

theorem Stochastic.tensor [Fintype Y₁] [Fintype Y₂] {k : Kernel X₁ Y₁} {l : Kernel X₂ Y₂}
    (hk : Stochastic k) (hl : Stochastic l) : Stochastic (tensor k l) :=
  ⟨hk.1.tensor hl.1, hk.2.tensor hl.2⟩

theorem Stochastic.ofFun [Fintype Y] [DecidableEq Y] (f : X → Y) : Stochastic (ofFun f) :=
  ⟨Nonneg.ofFun f, Normalised.ofFun f⟩

/-! ### Category laws (Julia testset "category laws") -/

theorem comp_assoc [Fintype Y] [Fintype Z] (k : Kernel X Y) (l : Kernel Y Z) (m : Kernel Z W) :
    comp (comp k l) m = comp k (comp l m) := by
  funext x w
  simp only [comp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_assoc]

theorem idK_comp [Fintype X] [DecidableEq X] (k : Kernel X Y) : comp (idK X) k = k := by
  rw [idK, comp_ofFun_left]; rfl

theorem comp_idK [Fintype Y] [DecidableEq Y] (k : Kernel X Y) : comp k (idK Y) = k := by
  rw [idK]; exact comp_ofEquiv_right k (Equiv.refl Y)

/-! ### Monoidal laws (Julia testset "monoidal laws") -/

/-- Interchange: `compose(otimes(k, l), otimes(k', l')) = otimes(compose(k, k'), compose(l, l'))`. -/
theorem comp_tensor [Fintype Y₁] [Fintype Y₂] (k : Kernel X₁ Y₁) (l : Kernel X₂ Y₂)
    (k' : Kernel Y₁ Z₁) (l' : Kernel Y₂ Z₂) :
    comp (tensor k l) (tensor k' l') = tensor (comp k k') (comp l l') := by
  funext x z
  simp only [comp_apply, tensor_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun y₁ _ => Finset.sum_congr rfl fun y₂ _ => by ring

/-- `otimes(id(X), id(Y)) = id(otimes(X, Y))`. -/
theorem tensor_idK [DecidableEq X] [DecidableEq Y] : tensor (idK X) (idK Y) = idK (X × Y) := by
  simp only [idK, tensor_ofFun]; rfl

/-- Associativity of the tensor, up to the associator:
`otimes(otimes(k, l), m) ⋅ α = α ⋅ otimes(k, otimes(l, m))`. -/
theorem tensor_assoc [Fintype X₁] [Fintype X₂] [Fintype X₃] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    [DecidableEq X₁] [DecidableEq X₂] [DecidableEq X₃] [DecidableEq Y₁] [DecidableEq Y₂]
    [DecidableEq Y₃] (k : Kernel X₁ Y₁) (l : Kernel X₂ Y₂) (m : Kernel X₃ Y₃) :
    comp (tensor (tensor k l) m) (assoc Y₁ Y₂ Y₃) = comp (assoc X₁ X₂ X₃) (tensor k (tensor l m)) := by
  rw [assoc, assoc, comp_ofEquiv_right, comp_ofFun_left]
  funext x y
  rcases x with ⟨⟨x₁, x₂⟩, x₃⟩; rcases y with ⟨y₁, y₂, y₃⟩
  simp [mul_assoc]

/-- Right unit of the tensor, up to the right unitor: `otimes(k, id(I)) ⋅ ρ = ρ ⋅ k`. -/
theorem tensor_unit_right [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (k : Kernel X Y) :
    comp (tensor k (idK Unit)) (rightUnitor Y) = comp (rightUnitor X) k := by
  rw [rightUnitor, rightUnitor, comp_ofEquiv_right, comp_ofFun_left]
  funext x y
  simp [idK]

/-- Left unit of the tensor, up to the left unitor: `otimes(id(I), k) ⋅ λ = λ ⋅ k`. -/
theorem tensor_unit_left [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (k : Kernel X Y) :
    comp (tensor (idK Unit) k) (leftUnitor Y) = comp (leftUnitor X) k := by
  rw [leftUnitor, leftUnitor, comp_ofEquiv_right, comp_ofFun_left]
  funext x y
  simp [idK]

/-- The symmetry is an involution: `braid(X, Y) ⋅ braid(Y, X) = id(X ⊗ Y)`. -/
theorem swap_swap [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    comp (swap X Y) (swap Y X) = idK (X × Y) := by
  rw [swap, swap, ofFun_comp_ofFun, idK]; rfl

/-- Naturality of the symmetry: `otimes(k, l) ⋅ braid = braid ⋅ otimes(l, k)`. -/
theorem tensor_swap [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂] [DecidableEq X₁]
    [DecidableEq X₂] [DecidableEq Y₁] [DecidableEq Y₂] (k : Kernel X₁ Y₁) (l : Kernel X₂ Y₂) :
    comp (tensor k l) (swap Y₁ Y₂) = comp (swap X₁ X₂) (tensor l k) := by
  rw [swap, swap, comp_ofEquiv_right, comp_ofFun_left]
  funext x y
  simp [mul_comm]

/-- The hexagon identity (`SymmetricCategory`/`BraidedCategory.hexagon_forward`), which is the
associator-explicit form of the Julia test
`braid(X ⊗ Y, Z) = (id(X) ⊗ braid(Y, Z)) ⋅ (braid(X, Z) ⊗ id(Y))`. -/
theorem hexagon [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] :
    comp (assoc X Y Z) (comp (swap X (Y × Z)) (assoc Y Z X)) =
      comp (tensor (swap X Y) (idK Z)) (comp (assoc Y X Z) (tensor (idK Y) (swap X Z))) := by
  simp only [assoc, swap, idK, tensor_ofFun, ofFun_comp_ofFun]
  rfl

/-- `braid(X, I) = id(X)` up to the unitors. -/
theorem swap_unit_right [Fintype X] [DecidableEq X] :
    comp (swap X Unit) (leftUnitor X) = rightUnitor X := by
  simp only [swap, leftUnitor, rightUnitor, ofFun_comp_ofFun]
  rfl

/-! ### Comonoid laws (Julia testsets "comonoid laws" and "coherence of copy and discard").

Each is named after the Mathlib field it instantiates; see `Theory/Correspondence.lean`. -/

/-- Coassociativity, `ComonObj.comul_assoc`: `Δ ≫ (X ◁ Δ) = Δ ≫ (Δ ▷ X) ≫ α`. -/
theorem copy_assoc [Fintype X] [DecidableEq X] :
    comp (copy X) (tensor (idK X) (copy X)) =
      comp (comp (copy X) (tensor (copy X) (idK X))) (assoc X X X) := by
  simp only [copy, idK, assoc, tensor_ofFun, ofFun_comp_ofFun]
  rfl

/-- Left counit, `ComonObj.counit_comul`: `Δ ≫ (ε ▷ X) = (λ_ X).inv`. -/
theorem copy_discard_left [Fintype X] [DecidableEq X] :
    comp (copy X) (tensor (discard X) (idK X)) = leftUnitorInv X := by
  simp only [copy, idK, discard_eq_ofFun, leftUnitorInv, tensor_ofFun, ofFun_comp_ofFun]
  rfl

/-- Right counit, `ComonObj.comul_counit`: `Δ ≫ (X ◁ ε) = (ρ_ X).inv`. -/
theorem copy_discard_right [Fintype X] [DecidableEq X] :
    comp (copy X) (tensor (idK X) (discard X)) = rightUnitorInv X := by
  simp only [copy, idK, discard_eq_ofFun, rightUnitorInv, tensor_ofFun, ofFun_comp_ofFun]
  rfl

/-- The strict form of the counit laws checked in Julia: `Δ(X) ⋅ (◊(X) ⊗ id(X)) = id(X)`. -/
theorem copy_discard_left_strict [Fintype X] [DecidableEq X] :
    comp (comp (copy X) (tensor (discard X) (idK X))) (leftUnitor X) = idK X := by
  rw [copy_discard_left, leftUnitorInv, leftUnitor, ofFun_comp_ofFun, idK]
  exact ofFun_congr fun x => by simp

/-- `Δ(X) ⋅ (id(X) ⊗ ◊(X)) = id(X)`. -/
theorem copy_discard_right_strict [Fintype X] [DecidableEq X] :
    comp (comp (copy X) (tensor (idK X) (discard X))) (rightUnitor X) = idK X := by
  rw [copy_discard_right, rightUnitorInv, rightUnitor, ofFun_comp_ofFun, idK]
  exact ofFun_congr fun x => by simp

/-- Cocommutativity, `IsCommComonObj.comul_comm`: `Δ ≫ β = Δ`. -/
theorem copy_swap [Fintype X] [DecidableEq X] : comp (copy X) (swap X X) = copy X := by
  simp only [copy, swap, ofFun_comp_ofFun]
  rfl

/-- Coherence of copy with the tensor, `CopyDiscardCategory.copy_tensor`:
`Δ[X ⊗ Y] = (Δ[X] ⊗ Δ[Y]) ≫ tensorμ`, Catlab's `Δ(A ⊗ B) = (Δ(A) ⊗ Δ(B)) ⋅ (id(A) ⊗ σ(A,B) ⊗ id(B))`. -/
theorem copy_prod [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    copy (X × Y) = comp (tensor (copy X) (copy Y)) (tensorμ X Y) := by
  simp only [copy, tensorμ, tensor_ofFun, ofFun_comp_ofFun]
  rfl

/-- Coherence of discard with the tensor, `CopyDiscardCategory.discard_tensor`:
`ε[X ⊗ Y] = (ε[X] ⊗ ε[Y]) ≫ (λ_ I).hom`, Catlab's `◊(A ⊗ B) = ◊(A) ⊗ ◊(B)`. -/
theorem discard_prod [Fintype X] [Fintype Y] :
    discard (X × Y) = comp (tensor (discard X) (discard Y)) unitMul := by
  funext x u
  simp [unitMul]

/-- `CopyDiscardCategory.copy_unit`: `Δ[I] = (λ_ I).inv`, Catlab's `Δ(munit()) = id(munit())`. -/
theorem copy_unit : copy Unit = leftUnitorInv Unit := rfl

/-- `CopyDiscardCategory.discard_unit`: `ε[I] = 𝟙 I`, Catlab's `◊(munit()) = id(munit())`. -/
theorem discard_unit : discard Unit = idK Unit := by
  funext x u; simp [idK]

/-- Every deterministic kernel is a comonoid homomorphism: it commutes with copy
(`Deterministic.copy_natural`, the equation the Julia test checks for `deterministic(X, Y, f)`). -/
theorem ofFun_copy_natural [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    comp (ofFun f) (copy Y) = comp (copy X) (tensor (ofFun f) (ofFun f)) := by
  simp only [copy, tensor_ofFun, ofFun_comp_ofFun]
  rfl

/-- ... and with discard (`Deterministic.discard_natural`). -/
theorem ofFun_discard_natural [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) :
    comp (ofFun f) (discard Y) = discard X := by
  rw [comp_ofFun_left]; rfl

end Kernel

end FiniteKernelsProofs.Finite
