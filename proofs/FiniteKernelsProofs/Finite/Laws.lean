import FiniteKernelsProofs.Finite.Kernel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# FiniteKernelsProofs.Finite.Laws

The two facts that `FiniteKernels.jl` pins numerically in `test/test_laws.jl` and that
separate a Markov category from a cartesian one, proved exactly for the finite model of
`Finite/Kernel.lean`:

* **Discard naturality iff normalised** (`comp_discard_eq_discard_iff`): the Markov axiom
  `f ⋅ ◊(B) == ◊(A)` holds for a table precisely when it is normalised. Julia testset
  "discard naturality iff normalised", including the `[0.5 0.5; 1.0 0.5]` counterexample
  (`comp_discard_apply` gives the column sums `[1.5, 1.0]`).
* **Copy naturality iff deterministic** (`comp_copy_eq_iff_isDeterministic`): for a normalised
  kernel, `f ⋅ Δ(B) == Δ(A) ⋅ (f ⊗ f)` holds iff every column is a point mass. Julia: "copy is
  natural for deterministic kernels only".
* **Copy versus tensor** (`comp_copy_eq_tensor_iff_isPointMass`): the special case of a state
  `p : I → X`; `compose(p, mcopy(X)) = otimes(p, p)` (modulo `I ⊗ I ≅ I`, which is `copy Unit`)
  iff `p` is a point mass. Julia testset "copy once is not two samples (SPEC section 6)".

The one piece of real arithmetic is `exists_pointMass_of_mul`: if `q x * q x' = [x = x'] q x`
and `∑ q = 1`, then `q` is an indicator. From `q x * q x = q x` one gets `q x ∈ {0, 1}`; the sum
forces at least one `1`; and `q x * q a = 0` for `x ≠ a` forces the rest to be `0`.
-/

namespace FiniteKernelsProofs.Finite.Kernel

open Finset

variable {X Y : Type}

/-! ### Discard naturality iff normalised -/

/-- `compose(k, delete(Y))` is the table of column sums. -/
theorem comp_discard_apply [Fintype Y] (k : Kernel X Y) (x : X) (u : Unit) :
    comp k (discard Y) x u = ∑ y, k x y := by
  simp

/-- The Markov axiom `f ⋅ ◊(B) == ◊(A)` holds for a table iff the table is normalised. -/
theorem comp_discard_eq_discard_iff [Fintype Y] (k : Kernel X Y) :
    comp k (discard Y) = discard X ↔ Normalised k := by
  constructor
  · intro h x
    have := congrFun (congrFun h x) ()
    simpa using this
  · intro h
    funext x u
    simp [h x]

/-- Discard is natural for normalised kernels (`MarkovCategory.discard_natural`). -/
theorem Normalised.comp_discard [Fintype Y] {k : Kernel X Y} (hk : Normalised k) :
    Kernel.comp k (Kernel.discard Y) = Kernel.discard X :=
  (comp_discard_eq_discard_iff k).mpr hk

/-- A normalised state has total mass one (`state_discard` in `BayesianNetworksProofs`). -/
theorem Normalised.state_discard [Fintype X] {p : State X} (hp : Normalised p) :
    Kernel.comp p (Kernel.discard X) = Kernel.idK Unit := by
  rw [hp.comp_discard, discard_unit]

/-! ### The indicator lemma -/

/-- If `q x * q x' = [x = x'] q x` and `∑ q = 1` then `q` is the indicator of a single point. -/
theorem exists_pointMass_of_mul [Fintype X] [DecidableEq X] (q : X → ℝ) (hsum : ∑ x, q x = 1)
    (h : ∀ x x', q x * q x' = if x = x' then q x else 0) :
    ∃ a, ∀ x, q x = if x = a then 1 else 0 := by
  have h01 : ∀ x, q x = 0 ∨ q x = 1 := by
    intro x
    have hx := h x x
    rw [if_pos rfl] at hx
    have : q x * (q x - 1) = 0 := by rw [mul_sub, mul_one, hx, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hex : ∃ a, q a = 1 := by
    by_contra hne
    push Not at hne
    have hzero : ∀ x, q x = 0 := fun x => (h01 x).resolve_right (hne x)
    have : ∑ x, q x = 0 := Finset.sum_eq_zero fun x _ => hzero x
    rw [this] at hsum
    exact zero_ne_one hsum
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, fun x => ?_⟩
  by_cases hxa : x = a
  · subst hxa; simp [ha]
  · have hx := h x a
    rw [if_neg hxa, ha, mul_one] at hx
    simp [hxa, hx]

/-- Conversely, an indicator satisfies the product identity. -/
theorem mul_ite_eq_of_pointMass [DecidableEq X] (a x x' : X) :
    (if x = a then (1 : ℝ) else 0) * (if x' = a then 1 else 0) =
      if x = x' then (if x = a then 1 else 0) else 0 := by
  by_cases hx : x = a
  · subst hx
    by_cases hx' : x' = x
    · subst hx'; simp
    · simp [hx', Ne.symm hx']
  · by_cases hx' : x' = a
    · subst hx'; simp [hx]
    · simp [hx, hx']

/-! ### Copy naturality iff deterministic -/

/-- `compose(k, mcopy(Y))` puts the column of `k` on the diagonal (draw once, then copy). -/
theorem comp_copy_apply [Fintype Y] [DecidableEq Y] (k : Kernel X Y) (x : X) (y₁ y₂ : Y) :
    comp k (copy Y) x (y₁, y₂) = if y₁ = y₂ then k x y₁ else 0 := by
  simp only [comp_apply, copy, ofFun_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  by_cases h : y₁ = y₂
  · subst h
    simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h rfl

/-- `compose(mcopy(X), otimes(k, k))` is the outer product of the column with itself
(draw twice, independently). -/
theorem copy_comp_tensor_apply [Fintype X] [DecidableEq X] (k : Kernel X Y) (x : X) (y₁ y₂ : Y) :
    comp (copy X) (tensor k k) x (y₁, y₂) = k x y₁ * k x y₂ := by
  simp [copy]

/-- For a normalised kernel, `f ⋅ Δ(B) == Δ(A) ⋅ (f ⊗ f)` holds iff `f` is deterministic. -/
theorem comp_copy_eq_iff_isDeterministic [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (k : Kernel X Y) (hk : Normalised k) :
    comp k (copy Y) = comp (copy X) (tensor k k) ↔ IsDeterministic k := by
  constructor
  · intro h x
    refine exists_pointMass_of_mul (k x) (hk x) fun y₁ y₂ => ?_
    have := congrFun (congrFun h x) (y₁, y₂)
    rw [comp_copy_apply, copy_comp_tensor_apply] at this
    exact this.symm
  · intro h
    funext x y
    rcases y with ⟨y₁, y₂⟩
    obtain ⟨a, ha⟩ := h x
    rw [comp_copy_apply, copy_comp_tensor_apply, ha y₁, ha y₂]
    exact (mul_ite_eq_of_pointMass a y₁ y₂).symm

/-- Deterministic kernels are exactly the `ofFun f` (Julia `deterministic(X, Y, f)`). -/
theorem isDeterministic_iff_exists_ofFun [DecidableEq Y] (k : Kernel X Y) :
    IsDeterministic k ↔ ∃ f : X → Y, k = ofFun f := by
  constructor
  · intro h
    choose f hf using h
    exact ⟨f, funext fun x => funext fun y => hf x y⟩
  · rintro ⟨f, rfl⟩ x
    exact ⟨f x, fun _ => rfl⟩

/-- Deterministic kernels are normalised. -/
theorem IsDeterministic.normalised [Fintype Y] [DecidableEq Y] {k : Kernel X Y}
    (h : IsDeterministic k) : Normalised k := by
  obtain ⟨f, rfl⟩ := (isDeterministic_iff_exists_ofFun k).mp h
  exact Normalised.ofFun f

/-! ### Copy versus tensor for states -/

theorem isPointMass_iff_isDeterministic [DecidableEq X] (p : State X) :
    IsPointMass p ↔ IsDeterministic p := by
  constructor
  · rintro ⟨a, ha⟩ _; exact ⟨a, ha⟩
  · intro h; exact h ()

theorem isPointMass_iff_exists_pointMass [DecidableEq X] (p : State X) :
    IsPointMass p ↔ ∃ a, p = pointMass a := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun u => funext fun x => by cases u; exact ha x⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, fun x => rfl⟩

/-- **Copy once is not two samples.** For a normalised state `p`, drawing once and copying
(`compose(p, mcopy(X))`) equals drawing twice independently (`otimes(p, p)`, with the domain
`I ⊗ I` identified with `I` by `copy Unit`) iff `p` is a point mass. -/
theorem comp_copy_eq_tensor_iff_isPointMass [Fintype X] [DecidableEq X] (p : State X)
    (hp : Normalised p) :
    comp p (copy X) = comp (copy Unit) (tensor p p) ↔ IsPointMass p := by
  rw [comp_copy_eq_iff_isDeterministic p hp, isPointMass_iff_isDeterministic]

/-- The same statement entrywise, without the `I ⊗ I ≅ I` reindexing:
`copied.table == independent.table` iff `p` is a point mass. -/
theorem comp_copy_eq_tensor_iff_isPointMass' [Fintype X] [DecidableEq X] (p : State X)
    (hp : Normalised p) :
    (∀ x x', comp p (copy X) () (x, x') = tensor p p ((), ()) (x, x')) ↔ IsPointMass p := by
  rw [← comp_copy_eq_tensor_iff_isPointMass p hp]
  constructor
  · intro h
    funext u y
    rcases y with ⟨x, x'⟩
    cases u
    rw [copy_comp_tensor_apply]
    exact h x x'
  · intro h x x'
    have := congrFun (congrFun h ()) (x, x')
    rw [copy_comp_tensor_apply] at this
    exact this

/-- Point masses do satisfy the equation (Julia: `compose(q, mcopy(X)) ≈ otimes(q, q)` for
`q = point_mass(X, l)`). -/
theorem pointMass_comp_copy [Fintype X] [DecidableEq X] (a : X) :
    comp (pointMass a) (copy X) = comp (copy Unit) (tensor (pointMass a) (pointMass a)) :=
  (comp_copy_eq_tensor_iff_isPointMass _ (Normalised.pointMass a)).mpr ⟨a, fun _ => rfl⟩

/-- The uniform state on two points is not a point mass, so for it the equation fails
(the Julia `state(X, [0.2, 0.3, 0.5])` example, in its smallest form). -/
example : ¬ IsPointMass (fun _ _ => (1 / 2 : ℝ) : State (Fin 2)) := by
  rintro ⟨a, ha⟩
  have := ha a
  norm_num at this

example :
    comp (fun _ _ => (1 / 2 : ℝ) : State (Fin 2)) (copy (Fin 2)) ≠
      comp (copy Unit) (tensor (fun _ _ => (1 / 2 : ℝ)) (fun _ _ => (1 / 2 : ℝ))) := by
  rw [Ne, comp_copy_eq_tensor_iff_isPointMass _ (fun _ => by simp)]
  rintro ⟨a, ha⟩
  have := ha a
  norm_num at this

end FiniteKernelsProofs.Finite.Kernel
