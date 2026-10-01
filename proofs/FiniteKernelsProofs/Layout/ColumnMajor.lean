import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.Ring

/-!
# Column-major multi-axis arrays

Julia stores an `Array{T,N}` as one flat vector in **column-major** order: the first axis varies
fastest. This module models that storage exactly, with no floating point and values in an
arbitrary type.

* A shape is a list of axis sizes `ns = [n₁, …, n_N]` (`size(table)`); `MIdx ns` is the type
  of in-bounds multi-indices, one `Fin nₖ` per axis (0-based), and `ns.prod` is `length(table)`.
* `lin idx = i₁ + n₁ * (i₂ + n₂ * (i₃ + …))` is the 0-based linear position. `lin_eq_sum_stride`
  gives the stride form `∑ₖ iₖ * ∏_{j<k} n_j`, and `juliaLinearIndex_coords` shows that the
  1-based fold `_linear_index` of `FiniteKernels.jl` (`src/kernels.jl`) computes `lin idx + 1`.
* `toFlat ns : MIdx ns ≃ Fin ns.prod` has value `lin` (`toFlat_val`): **the linear index is a
  bijection between multi-indices and flat positions**. `Tensor α ns := Fin ns.prod → α` is a
  flat table, and `Tensor.equivFun` identifies flat tables with functions of the multi-index.
* `MIdx.append` concatenates multi-indices (`(y..., x...)`), and
  `lin (append y x) = lin y + ns.prod * lin x` (`lin_append`): the flat table of shape
  `ns ++ ms` is a column-major `ns.prod × ms.prod` matrix (`reshape`).
* `MIdx.next` is the column-major odometer: `lin (next idx) = (lin idx + 1) % ns.prod`.

The labels of `FiniteAxis` are not modelled: an index is a label position (`label_index` minus
one). The statements are about index arithmetic, not about Julia execution.
-/

namespace FiniteKernelsProofs.Layout

/-- In-bounds multi-indices of a shape, one 0-based coordinate per axis, first axis first. -/
def MIdx : List ℕ → Type
  | [] => Unit
  | n :: ns => Fin n × MIdx ns

namespace MIdx

/-- The empty multi-index of the zero-dimensional shape. -/
def nil : MIdx [] := ()

/-- Prepend a coordinate on a new first axis. -/
def cons {n : ℕ} {ns : List ℕ} (i : Fin n) (r : MIdx ns) : MIdx (n :: ns) := (i, r)

/-- The coordinate of the first axis. -/
def head {n : ℕ} {ns : List ℕ} (idx : MIdx (n :: ns)) : Fin n := Prod.fst idx

/-- The coordinates of the remaining axes. -/
def tail {n : ℕ} {ns : List ℕ} (idx : MIdx (n :: ns)) : MIdx ns := Prod.snd idx

@[simp] theorem head_cons {n : ℕ} {ns : List ℕ} (i : Fin n) (r : MIdx ns) :
    head (cons i r) = i := rfl

@[simp] theorem tail_cons {n : ℕ} {ns : List ℕ} (i : Fin n) (r : MIdx ns) :
    tail (cons i r) = r := rfl

@[simp] theorem cons_head_tail {n : ℕ} {ns : List ℕ} (idx : MIdx (n :: ns)) :
    cons (head idx) (tail idx) = idx := rfl

theorem ext_nil (a b : MIdx []) : a = b := rfl

theorem ext_cons {n : ℕ} {ns : List ℕ} {a b : MIdx (n :: ns)} (h1 : head a = head b)
    (h2 : tail a = tail b) : a = b := Prod.ext h1 h2

instance instDecidableEq : (ns : List ℕ) → DecidableEq (MIdx ns)
  | [] => inferInstanceAs (DecidableEq Unit)
  | n :: ns => @instDecidableEqProd (Fin n) (MIdx ns) _ (instDecidableEq ns)

/-- The coordinate list `(i₁, …, i_N)` (0-based), as Julia's `Tuple(CartesianIndex) .- 1`. -/
def coords : {ns : List ℕ} → MIdx ns → List ℕ
  | [], _ => []
  | _ :: _, idx => (head idx : ℕ) :: coords (tail idx)

@[simp] theorem coords_nil (idx : MIdx []) : coords idx = [] := rfl

@[simp] theorem coords_cons {n : ℕ} {ns : List ℕ} (i : Fin n) (r : MIdx ns) :
    coords (cons i r) = (i : ℕ) :: coords r := rfl

theorem length_coords : {ns : List ℕ} → (idx : MIdx ns) → (coords idx).length = ns.length
  | [], _ => rfl
  | _ :: _, idx => by simp [coords, length_coords (tail idx)]

/-- A multi-index is determined by its coordinate list. -/
theorem coords_injective : {ns : List ℕ} → Function.Injective (@coords ns)
  | [], a, b, _ => ext_nil a b
  | _ :: _, a, b, h => by
    simp only [coords, List.cons.injEq] at h
    exact ext_cons (Fin.ext h.1) (coords_injective h.2)

/-- Concatenation `(y..., x...)` of multi-indices. -/
def append : {ns ms : List ℕ} → MIdx ns → MIdx ms → MIdx (ns ++ ms)
  | [], _, _, x => x
  | _ :: _, _, y, x => cons (head y) (append (tail y) x)

/-- The prefix of a multi-index on `ns ++ ms`. -/
def fst : {ns ms : List ℕ} → MIdx (ns ++ ms) → MIdx ns
  | [], _, _ => ()
  | _ :: _, _, z => cons (head z) (fst (ns := _) (tail z))

/-- The suffix of a multi-index on `ns ++ ms`. -/
def snd : {ns ms : List ℕ} → MIdx (ns ++ ms) → MIdx ms
  | [], _, z => z
  | _ :: _, _, z => snd (ns := _) (tail z)

theorem fst_append : {ns ms : List ℕ} → (y : MIdx ns) → (x : MIdx ms) → fst (append y x) = y
  | [], _, _, _ => rfl
  | _ :: _, _, y, x => by
    show cons (head y) (fst (append (tail y) x)) = y
    rw [fst_append]; rfl

theorem snd_append : {ns ms : List ℕ} → (y : MIdx ns) → (x : MIdx ms) → snd (append y x) = x
  | [], _, _, _ => rfl
  | _ :: _, _, y, x => snd_append (tail y) x

theorem append_fst_snd : {ns ms : List ℕ} → (z : MIdx (ns ++ ms)) → append (fst z) (snd z) = z
  | [], _, _ => rfl
  | _ :: ns, ms, z => by
    show cons (head z) (append (fst (ns := ns) (ms := ms) (tail z)) (snd (tail z))) = z
    rw [append_fst_snd]; rfl

/-- Multi-indices of `ns ++ ms` are pairs of multi-indices. -/
def appendEquiv (ns ms : List ℕ) : MIdx ns × MIdx ms ≃ MIdx (ns ++ ms) where
  toFun p := append p.1 p.2
  invFun z := (fst z, snd z)
  left_inv p := by simp [fst_append, snd_append]
  right_inv z := append_fst_snd z

theorem coords_append : {ns ms : List ℕ} → (y : MIdx ns) → (x : MIdx ms) →
    coords (append y x) = coords y ++ coords x
  | [], _, _, _ => rfl
  | _ :: _, _, y, x => by
    show (head y : ℕ) :: coords (append (tail y) x) = ((head y : ℕ) :: coords (tail y)) ++ coords x
    rw [coords_append]; rfl

/-! ### The linear index -/

/-- The 0-based column-major position: `i₁ + n₁ * (i₂ + n₂ * (…))`. -/
def lin : {ns : List ℕ} → MIdx ns → ℕ
  | [], _ => 0
  | n :: _, idx => (head idx : ℕ) + n * lin (tail idx)

@[simp] theorem lin_nil (idx : MIdx []) : lin idx = 0 := rfl

@[simp] theorem lin_cons {n : ℕ} {ns : List ℕ} (i : Fin n) (r : MIdx ns) :
    lin (cons i r) = i + n * lin r := rfl

theorem lin_lt : {ns : List ℕ} → (idx : MIdx ns) → lin idx < ns.prod
  | [], _ => by simp [lin]
  | n :: _, idx => by
    have h1 := lin_lt (tail idx)
    have h2 := (head idx).isLt
    simp only [lin, List.prod_cons]
    calc (head idx : ℕ) + n * lin (tail idx) < n + n * lin (tail idx) := by omega
      _ = n * (lin (tail idx) + 1) := by ring
      _ ≤ n * _ := Nat.mul_le_mul_left _ h1

/-- The column-major stride of axis `k`: the product of the sizes of the axes before it. -/
def stride (ns : List ℕ) (k : ℕ) : ℕ := (ns.take k).prod

/-- **Stride form of the linear index**: `lin idx = ∑ₖ iₖ * stride k`, with
`stride k = ∏_{j<k} n_j` (the first axis has stride one). -/
theorem lin_eq_sum_stride : {ns : List ℕ} → (idx : MIdx ns) →
    lin idx = ∑ k ∈ Finset.range ns.length, (coords idx).getD k 0 * stride ns k
  | [], _ => by simp [lin]
  | n :: ns, idx => by
    rw [show idx = cons (head idx) (tail idx) from rfl, List.length_cons, Finset.sum_range_succ',
      lin_cons, coords_cons, lin_eq_sum_stride (tail idx), Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, stride, List.take_succ_cons,
      List.prod_cons, List.take_zero, List.prod_nil, mul_one]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The 1-based fold of `_linear_index(dims, idx)` in `FiniteKernels.jl`:
`lin = 1; stride = 1; for (d, i) in zip(dims, idx); lin += (i - 1) * stride; stride *= d; end`. -/
def juliaLinearIndex (dims idx : List ℕ) : ℕ :=
  ((dims.zip idx).foldl (fun acc p => (acc.1 + (p.2 - 1) * acc.2, acc.2 * p.1)) (1, 1)).1

theorem foldl_linear : {ns : List ℕ} → (idx : MIdx ns) → (a s : ℕ) →
    (ns.zip ((coords idx).map (· + 1))).foldl
        (fun acc p => (acc.1 + (p.2 - 1) * acc.2, acc.2 * p.1)) (a, s) =
      (a + s * lin idx, s * ns.prod)
  | [], _, a, s => by simp [lin]
  | n :: ns, idx, a, s => by
    rw [show idx = cons (head idx) (tail idx) from rfl]
    simp only [coords_cons, List.map_cons, List.zip_cons_cons, List.foldl_cons,
      Nat.add_sub_cancel, lin_cons, List.prod_cons]
    rw [foldl_linear (tail idx)]
    ext <;> simp only <;> ring

/-- **Julia's `_linear_index` is the column-major position**, shifted to 1-based. -/
theorem juliaLinearIndex_coords {ns : List ℕ} (idx : MIdx ns) :
    juliaLinearIndex ns ((coords idx).map (· + 1)) = lin idx + 1 := by
  simp [juliaLinearIndex, foldl_linear, add_comm]

/-! ### The bijection with flat positions -/

/-- Multi-indices of a shape are in bijection with the flat positions `Fin ns.prod`. -/
def toFlat : (ns : List ℕ) → MIdx ns ≃ Fin ns.prod
  | [] =>
    { toFun := fun _ => ⟨0, by simp⟩
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun p => Fin.ext (by
        have h : (p : ℕ) < 1 := p.isLt
        show 0 = (p : ℕ)
        omega) }
  | n :: ns =>
    ((Equiv.prodCongr (Equiv.refl (Fin n)) (toFlat ns)).trans (Equiv.prodComm _ _)).trans
      (finProdFinEquiv.trans (finCongr (by simp [Nat.mul_comm])))

/-- **The flat position of a multi-index is its column-major linear index.** -/
@[simp] theorem toFlat_val : {ns : List ℕ} → (idx : MIdx ns) → (toFlat ns idx : ℕ) = lin idx
  | [], _ => rfl
  | n :: ns, idx => by
    have h := toFlat_val (tail idx)
    simp only [toFlat]
    rw [lin]
    exact congrArg _ (congrArg _ h)

theorem lin_injective {ns : List ℕ} : Function.Injective (@lin ns) := by
  intro a b h
  apply (toFlat ns).injective
  exact Fin.ext (by simpa using h)

theorem lin_surjective {ns : List ℕ} (p : ℕ) (hp : p < ns.prod) : ∃ idx : MIdx ns, lin idx = p :=
  ⟨(toFlat ns).symm ⟨p, hp⟩, by rw [← toFlat_val, Equiv.apply_symm_apply]⟩

/-- **The column-major linear index is a bijection** from multi-indices onto the flat
positions `Fin ns.prod` (`Fin (prod(size(table)))`). -/
theorem linearIndex_bijective (ns : List ℕ) :
    Function.Bijective (fun idx : MIdx ns => (⟨lin idx, lin_lt idx⟩ : Fin ns.prod)) := by
  have h : (fun idx : MIdx ns => (⟨lin idx, lin_lt idx⟩ : Fin ns.prod)) = toFlat ns :=
    funext fun idx => Fin.ext (toFlat_val idx).symm
  rw [h]
  exact (toFlat ns).bijective

instance instFintype (ns : List ℕ) : Fintype (MIdx ns) := Fintype.ofEquiv _ (toFlat ns).symm

theorem card (ns : List ℕ) : Fintype.card (MIdx ns) = ns.prod := by
  rw [Fintype.card_congr (toFlat ns), Fintype.card_fin]

/-- **Concatenated multi-indices**: the flat table of shape `ns ++ ms` is the column-major
`ns.prod × ms.prod` matrix whose entry `[lin y, lin x]` sits at `lin (y..., x...)`. -/
theorem lin_append : {ns ms : List ℕ} → (y : MIdx ns) → (x : MIdx ms) →
    lin (append y x) = lin y + ns.prod * lin x
  | [], _, _, _ => by simp [append]
  | n :: ns, _, y, x => by
    show (head y : ℕ) + n * lin (append (tail y) x) = (head y : ℕ) + n * lin (tail y) +
      (n * ns.prod) * lin x
    rw [lin_append]
    ring

/-! ### The column-major odometer -/

/-- The next multi-index in column-major order, wrapping to all zeros after the last. -/
def next : {ns : List ℕ} → MIdx ns → MIdx ns
  | [], _ => ()
  | n :: _, idx =>
    if h : (head idx : ℕ) + 1 < n then cons ⟨head idx + 1, h⟩ (tail idx)
    else cons ⟨0, lt_of_le_of_lt (Nat.zero_le _) (head idx).isLt⟩ (next (tail idx))

theorem lin_next : {ns : List ℕ} → (idx : MIdx ns) → lin (next idx) = (lin idx + 1) % ns.prod
  | [], _ => by simp [lin]
  | n :: ns, idx => by
    have hi := (head idx).isLt
    have hr := lin_lt (tail idx)
    by_cases h : (head idx : ℕ) + 1 < n
    · have hlt : (head idx : ℕ) + n * lin (tail idx) + 1 < n * ns.prod :=
        calc (head idx : ℕ) + n * lin (tail idx) + 1 < n + n * lin (tail idx) := by omega
          _ = n * (lin (tail idx) + 1) := by ring
          _ ≤ n * ns.prod := Nat.mul_le_mul_left _ hr
      have hn : next idx = cons ⟨head idx + 1, h⟩ (tail idx) := dif_pos h
      rw [hn]
      show ((head idx : ℕ) + 1) + n * lin (tail idx) =
        ((head idx : ℕ) + n * lin (tail idx) + 1) % (n * ns.prod)
      rw [Nat.mod_eq_of_lt hlt]
      ring
    · have he : (head idx : ℕ) + 1 = n := by omega
      have hn : next idx = cons ⟨0, by omega⟩ (next (tail idx)) := dif_neg h
      have hs : (head idx : ℕ) + n * lin (tail idx) + 1 = n * (lin (tail idx) + 1) :=
        calc (head idx : ℕ) + n * lin (tail idx) + 1 = ((head idx : ℕ) + 1) + n * lin (tail idx) :=
              by ring
          _ = n + n * lin (tail idx) := by rw [he]
          _ = n * (lin (tail idx) + 1) := by ring
      rw [hn]
      show 0 + n * lin (next (tail idx)) =
        ((head idx : ℕ) + n * lin (tail idx) + 1) % (n * ns.prod)
      rw [lin_next (tail idx), zero_add, hs, Nat.mul_mod_mul_left]

/-- Stepping the odometer `p` times from position zero reaches flat position `p`. -/
theorem lin_iterate_next {ns : List ℕ} (z : MIdx ns) (hz : lin z = 0) (p : ℕ) :
    lin (next^[p] z) = p % ns.prod := by
  induction p with
  | zero =>
    rw [Function.iterate_zero, id_eq, hz, Nat.zero_mod]
  | succ p ih =>
    rw [Function.iterate_succ_apply', lin_next, ih, Nat.mod_add_mod]

end MIdx

/-! ## Flat tables -/

/-- A flat table of shape `ns`: `length(table) = ns.prod` values in column-major order
(`vec(table)`). -/
def Tensor (α : Type) (ns : List ℕ) : Type := Fin ns.prod → α

namespace Tensor

variable {α : Type} {ns : List ℕ}

/-- `table[i₁, …, i_N]`: the value stored at the column-major position of the multi-index. -/
def get (A : Tensor α ns) (idx : MIdx ns) : α := A (MIdx.toFlat ns idx)

/-- The flat table whose entry at every multi-index is `f idx`. -/
def ofFun (f : MIdx ns → α) : Tensor α ns := fun p => f ((MIdx.toFlat ns).symm p)

@[simp] theorem get_ofFun (f : MIdx ns → α) (idx : MIdx ns) : get (ofFun f) idx = f idx := by
  simp [get, ofFun]

@[simp] theorem ofFun_get (A : Tensor α ns) : ofFun (get A) = A := by
  funext p
  simp [get, ofFun]

theorem ext_get {A B : Tensor α ns} (h : ∀ idx, get A idx = get B idx) : A = B := by
  rw [← ofFun_get A, ← ofFun_get B]
  exact congrArg ofFun (funext h)

/-- Flat column-major tables are exactly functions of the multi-index. -/
def equivFun (α : Type) (ns : List ℕ) : Tensor α ns ≃ (MIdx ns → α) where
  toFun := get
  invFun := ofFun
  left_inv := ofFun_get
  right_inv f := funext (get_ofFun f)

/-- Reading the flat position whose 1-based index is Julia's `_linear_index` fold is `get`. -/
theorem get_eq_juliaLinearIndex (A : Tensor α ns) (idx : MIdx ns) (p : Fin ns.prod)
    (hp : (p : ℕ) + 1 = MIdx.juliaLinearIndex ns ((MIdx.coords idx).map (· + 1))) :
    get A idx = A p := by
  unfold get
  congr 1
  apply Fin.ext
  rw [MIdx.toFlat_val]
  rw [MIdx.juliaLinearIndex_coords] at hp
  omega

end Tensor

end FiniteKernelsProofs.Layout
