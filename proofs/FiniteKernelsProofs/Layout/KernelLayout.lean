import FiniteKernelsProofs.Layout.ColumnMajor
import FiniteKernelsProofs.Finite.Kernel

/-!
# The outputs-first kernel layout and the `(parents..., child)` CPT layout

`FiniteKernel.table` stores a kernel `dom → codom` **outputs first**:
`size(table) == (size(codom)..., size(dom)...)` and `table[y..., x...] = P(y | x)` (ADR 0002).
User CPTs are `(parents..., child)`, normalised over the last axis, and `cpt` is the only
conversion: `permutedims(table, (n + 1, 1, …, n))` one way, `permutedims(table, (2, …, n + 1, 1))`
the other.

* `KernelTable α cs ds := Tensor α (cs ++ ds)`; `toKernel T x y = table[y..., x...]` is a
  function of the input first, the convention of `Finite.Kernel` (for `α = ℝ` it *is* a
  `Finite.Kernel (MIdx ds) (MIdx cs)`), and `kernelEquiv` shows flat outputs-first tables and
  kernels are the same data.
* `kernelMatrix_toFlat`: the flat table read as the column-major
  `length(codom) × length(dom)` matrix (`kernel_matrix = reshape(table, …)`) has entry
  `P(y | x)` at row `lin y`, column `lin x`.
* `probability_linear`: `probability(k, y, x)` reads `_linear_index(size(table), (iy..., ix...))`,
  which is `lin (y..., x...) + 1`.
* `cptToKernel` / `kernelToCpt` model the two `permutedims` calls. They are mutually inverse
  (`cptEquiv`), so the permutation of flat storage positions `cptPerm` is a bijection, and every
  entry is preserved: `toKernel_cptToKernel` says that `P(child = i | parents = x)` read from the
  kernel is the CPT entry `table[x..., i]`. `cptToKernel_permutedims` and
  `kernelToCpt_permutedims` show that they satisfy Julia's `permutedims(A, perm)` contract
  `B[I] = A[J]` whenever `J[perm[k]] = I[k]`, for exactly the tuples `(n + 1, 1, …, n)` and
  `(2, …, n + 1, 1)` used in `src/kernels.jl`.
* `normalised_cptToKernel_iff`: the kernel is normalised iff every CPT row sums to one over the
  last (child) axis.

This links layouts and index arithmetic. It does not execute Julia, and the values are exact
(any type; `ℝ` for normalisation), not IEEE floating point.
-/

namespace FiniteKernelsProofs.Layout

open MIdx

variable {α : Type}

/-! ## Outputs-first kernel tables -/

/-- `FiniteKernel.table` for codomain shape `cs` and domain shape `ds`: outputs first. -/
abbrev KernelTable (α : Type) (cs ds : List ℕ) : Type := Tensor α (cs ++ ds)

namespace KernelTable

variable {cs ds : List ℕ}

/-- `table[y..., x...]`. -/
def entry (T : KernelTable α cs ds) (y : MIdx cs) (x : MIdx ds) : α := Tensor.get T (append y x)

/-- The kernel stored by an outputs-first table, input first: `toKernel T x y = P(y | x)`. -/
def toKernel (T : KernelTable α cs ds) : MIdx ds → MIdx cs → α := fun x y => T.entry y x

/-- The outputs-first table of a kernel. -/
def ofKernel (k : MIdx ds → MIdx cs → α) : KernelTable α cs ds :=
  Tensor.ofFun fun z => k (snd z) (fst z)

@[simp] theorem toKernel_ofKernel (k : MIdx ds → MIdx cs → α) : toKernel (ofKernel k) = k := by
  funext x y
  simp [toKernel, ofKernel, entry, fst_append, snd_append]

@[simp] theorem ofKernel_toKernel (T : KernelTable α cs ds) : ofKernel (toKernel T) = T := by
  apply Tensor.ext_get
  intro z
  simp [toKernel, ofKernel, entry, append_fst_snd]

/-- Flat outputs-first tables and kernels (input first) are the same data. -/
def kernelEquiv (α : Type) (cs ds : List ℕ) :
    KernelTable α cs ds ≃ (MIdx ds → MIdx cs → α) where
  toFun := toKernel
  invFun := ofKernel
  left_inv := ofKernel_toKernel
  right_inv := toKernel_ofKernel

/-- For real entries the stored kernel is a kernel of the finite model `Finite.Kernel`. -/
def toFiniteKernel (T : KernelTable ℝ cs ds) : Finite.Kernel (MIdx ds) (MIdx cs) := toKernel T

theorem prod_append (cs ds : List ℕ) : (cs ++ ds).prod = cs.prod * ds.prod := List.prod_append

/-- `kernel_matrix(k) = reshape(table, length(codom), length(dom))`, read column-major. -/
def kernelMatrix (T : KernelTable α cs ds) (r : Fin cs.prod) (c : Fin ds.prod) : α :=
  T ⟨r + cs.prod * c, by
    rw [prod_append]
    have hr := r.isLt
    have hc := c.isLt
    calc (r : ℕ) + cs.prod * c < cs.prod + cs.prod * c := by omega
      _ = cs.prod * (c + 1) := by ring
      _ ≤ cs.prod * ds.prod := Nat.mul_le_mul_left _ hc⟩

/-- **`kernel_matrix` has `P(y | x)` at row `lin y`, column `lin x`.** -/
theorem kernelMatrix_toFlat (T : KernelTable α cs ds) (y : MIdx cs) (x : MIdx ds) :
    kernelMatrix T (toFlat cs y) (toFlat ds x) = T.entry y x := by
  unfold kernelMatrix entry Tensor.get
  congr 1
  apply Fin.ext
  simp [lin_append]

/-- **`probability(k, y, x)` reads the entry `table[y..., x...]`**: Julia's 1-based
`_linear_index(size(table), (Tuple(iy)..., Tuple(ix)...))` is `lin (y..., x...) + 1`. -/
theorem probability_linear (y : MIdx cs) (x : MIdx ds) :
    juliaLinearIndex (cs ++ ds) ((coords y ++ coords x).map (· + 1)) =
      lin (append y x) + 1 := by
  rw [← coords_append, juliaLinearIndex_coords]

end KernelTable

/-! ## The `(parents..., child)` CPT layout and `cpt` -/

/-- A user CPT: shape `(parents..., child)`. -/
abbrev CptTable (α : Type) (ps : List ℕ) (c : ℕ) : Type := Tensor α (ps ++ [c])

/-- The multi-index of a single child axis. -/
def childIdx {c : ℕ} (i : Fin c) : MIdx [c] := cons i nil

@[simp] theorem head_childIdx {c : ℕ} (i : Fin c) : head (childIdx i) = i := rfl

theorem childIdx_head {c : ℕ} (y : MIdx [c]) : childIdx (head y) = y := rfl

namespace CptTable

variable {ps : List ℕ} {c : ℕ}

/-- `table[x..., i]`: the probability of child state `i` given parent states `x`. -/
def entry (A : CptTable α ps c) (x : MIdx ps) (i : Fin c) : α :=
  Tensor.get A (append x (childIdx i))

end CptTable

/-- `cpt(parents, child, table)`: `permutedims(table, (n + 1, 1, …, n))`, child axis first. -/
def cptToKernel {ps : List ℕ} {c : ℕ} (A : CptTable α ps c) : KernelTable α [c] ps :=
  Tensor.ofFun fun z => Tensor.get A (append (snd (ns := [c]) z) (fst (ns := [c]) z))

/-- `cpt(k)`: `permutedims(table, (2, …, n + 1, 1))`, back to parents first. -/
def kernelToCpt {ps : List ℕ} {c : ℕ} (T : KernelTable α [c] ps) : CptTable α ps c :=
  Tensor.ofFun fun w => Tensor.get T (append (snd (ns := ps) w) (fst (ns := ps) w))

theorem get_cptToKernel {ps : List ℕ} {c : ℕ} (A : CptTable α ps c) (y : MIdx [c])
    (x : MIdx ps) : Tensor.get (cptToKernel A) (append y x) = Tensor.get A (append x y) := by
  simp [cptToKernel, fst_append, snd_append]

theorem get_kernelToCpt {ps : List ℕ} {c : ℕ} (T : KernelTable α [c] ps) (x : MIdx ps)
    (y : MIdx [c]) : Tensor.get (kernelToCpt T) (append x y) = Tensor.get T (append y x) := by
  simp [kernelToCpt, fst_append, snd_append]

/-- **`cpt` preserves every entry**: the kernel built from a CPT gives
`P(child = i | parents = x) = table[x..., i]`. -/
theorem toKernel_cptToKernel {ps : List ℕ} {c : ℕ} (A : CptTable α ps c) (x : MIdx ps)
    (i : Fin c) : KernelTable.toKernel (cptToKernel A) x (childIdx i) = A.entry x i :=
  get_cptToKernel A (childIdx i) x

theorem entry_kernelToCpt {ps : List ℕ} {c : ℕ} (T : KernelTable α [c] ps) (x : MIdx ps)
    (i : Fin c) : (kernelToCpt T).entry x i = KernelTable.toKernel T x (childIdx i) :=
  get_kernelToCpt T x (childIdx i)

@[simp] theorem kernelToCpt_cptToKernel {ps : List ℕ} {c : ℕ} (A : CptTable α ps c) :
    kernelToCpt (cptToKernel A) = A := by
  apply Tensor.ext_get
  intro w
  rw [← append_fst_snd w, get_kernelToCpt, get_cptToKernel]

@[simp] theorem cptToKernel_kernelToCpt {ps : List ℕ} {c : ℕ} (T : KernelTable α [c] ps) :
    cptToKernel (kernelToCpt T) = T := by
  apply Tensor.ext_get
  intro z
  rw [← append_fst_snd (ns := [c]) z, get_cptToKernel, get_kernelToCpt]

/-- The two `cpt` conversions are mutually inverse. -/
def cptEquiv (α : Type) (ps : List ℕ) (c : ℕ) : CptTable α ps c ≃ KernelTable α [c] ps where
  toFun := cptToKernel
  invFun := kernelToCpt
  left_inv := kernelToCpt_cptToKernel
  right_inv := cptToKernel_kernelToCpt

/-- The permutation of flat storage positions that `cpt` performs. -/
def cptPerm (ps : List ℕ) (c : ℕ) : Fin (ps ++ [c]).prod ≃ Fin ([c] ++ ps).prod :=
  (toFlat (ps ++ [c])).symm.trans <| (appendEquiv ps [c]).symm.trans <|
    (Equiv.prodComm _ _).trans <| (appendEquiv [c] ps).trans (toFlat ([c] ++ ps))

/-- **`cpt` moves storage by a bijection of positions and copies every value**:
the kernel table at position `q` is the CPT value at position `cptPerm.symm q`. -/
theorem cptToKernel_apply {ps : List ℕ} {c : ℕ} (A : CptTable α ps c)
    (q : Fin ([c] ++ ps).prod) : cptToKernel A q = A ((cptPerm ps c).symm q) := by
  rfl

/-! ## Julia's `permutedims` contract -/

/-- `B = permutedims(A, perm)` (0-based `perm`): `size(B, k) = size(A, perm[k])` and
`B[I] = A[J]` whenever `J[perm[k]] = I[k]` for every axis `k`. -/
def PermutedimsSpec {ns ms : List ℕ} (perm : ℕ → ℕ) (A : Tensor α ns) (B : Tensor α ms) : Prop :=
  (∀ k < ms.length, ms[k]? = ns[perm k]?) ∧
    ∀ (I : MIdx ms) (J : MIdx ns),
      (∀ k < ms.length, (coords J)[perm k]? = (coords I)[k]?) → Tensor.get B I = Tensor.get A J

/-- The tuple `(n + 1, 1, …, n)` of `cpt(parents, child, table)`, 0-based. -/
def cptPermTuple (n : ℕ) (k : ℕ) : ℕ := if k = 0 then n else k - 1

/-- The tuple `(2, …, n + 1, 1)` of `cpt(k)`, 0-based. -/
def uncptPermTuple (n : ℕ) (k : ℕ) : ℕ := if k < n then k + 1 else 0

theorem coords_eq_of_perm {ps : List ℕ} {c : ℕ} (x : MIdx ps) (i : Fin c) (J : MIdx (ps ++ [c]))
    (h : ∀ k < ps.length + 1,
      (coords J)[cptPermTuple ps.length k]? = ((i : ℕ) :: coords x)[k]?) :
    J = append x (childIdx i) := by
  apply coords_injective
  rw [coords_append]
  apply List.ext_getElem?
  intro k
  have hJ := length_coords J
  have hx := length_coords x
  simp only [List.length_append, List.length_cons, List.length_nil] at hJ
  rcases lt_trichotomy k ps.length with hk | hk | hk
  · have := h (k + 1) (by omega)
    simp only [cptPermTuple, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
      List.getElem?_cons_succ] at this
    have hk' : k < (coords x).length := by omega
    rw [this, List.getElem?_append_left hk']
  · subst hk
    have := h 0 (by omega)
    simp only [cptPermTuple, if_true, List.getElem?_cons_zero] at this
    have hle : (coords x).length ≤ ps.length := le_of_eq hx
    rw [this, List.getElem?_append_right hle, hx, Nat.sub_self]
    all_goals rfl
  · have h1 : (coords J).length ≤ k := by omega
    have h2 : (coords x ++ coords (childIdx i)).length ≤ k := by
      rw [List.length_append, hx]
      show ps.length + 1 ≤ k
      omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

/-- **`cpt(parents, child, table)` is `permutedims(table, (n + 1, 1, …, n))`.** -/
theorem cptToKernel_permutedims {ps : List ℕ} {c : ℕ} (A : CptTable α ps c) :
    PermutedimsSpec (cptPermTuple ps.length) A (cptToKernel A) := by
  constructor
  · intro k hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [cptPermTuple]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : j < ps.length := by omega
      simp only [cptPermTuple, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      rw [List.getElem?_append_left (l₂ := [c]) hj]
      simp
  · intro I J hIJ
    have hI : I = append (fst (ns := [c]) I) (snd (ns := [c]) I) := (append_fst_snd I).symm
    have hc : coords I = (head (fst (ns := [c]) I) : ℕ) :: coords (snd (ns := [c]) I) := by
      conv_lhs => rw [hI]
      rw [coords_append]
      all_goals rfl
    have hJ : J = append (snd (ns := [c]) I) (childIdx (head (fst (ns := [c]) I))) := by
      apply coords_eq_of_perm
      intro k hk
      have hk' : k < ([c] ++ ps).length := by simp; omega
      rw [hIJ k hk', hc]
    rw [hJ]
    conv_lhs => rw [hI]
    rw [get_cptToKernel, childIdx_head]

/-- **`cpt(k)` is `permutedims(table, (2, …, n + 1, 1))`.** -/
theorem kernelToCpt_permutedims {ps : List ℕ} {c : ℕ} (T : KernelTable α [c] ps) :
    PermutedimsSpec (uncptPermTuple ps.length) T (kernelToCpt T) := by
  constructor
  · intro k hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    by_cases hkn : k < ps.length
    · simp only [uncptPermTuple, hkn, if_true]
      rw [List.getElem?_append_left (l₂ := [c]) hkn]
      simp
    · have : k = ps.length := by omega
      subst this
      simp [uncptPermTuple]
  · intro I J hIJ
    have hI : I = append (fst (ns := ps) I) (snd (ns := ps) I) := (append_fst_snd I).symm
    have hcI : coords I = coords (fst (ns := ps) (ms := [c]) I) ++
        [(head (snd (ns := ps) (ms := [c]) I) : ℕ)] := by
      conv_lhs => rw [hI]
      rw [coords_append]
      all_goals rfl
    have hy : coords (snd (ns := ps) (ms := [c]) I) = [(head (snd (ns := ps) (ms := [c]) I) : ℕ)] :=
      rfl
    have hx := length_coords (fst (ns := ps) (ms := [c]) I)
    have hJ : J = append (snd (ns := ps) (ms := [c]) I) (fst (ns := ps) (ms := [c]) I) := by
      apply coords_injective
      rw [coords_append]
      apply List.ext_getElem?
      intro k
      have hlen := length_coords J
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have := hIJ ps.length (by simp)
        simp only [uncptPermTuple, lt_irrefl, if_false] at this
        have hle : (coords (fst (ns := ps) (ms := [c]) I)).length ≤ ps.length := le_of_eq hx
        rw [this, hcI, List.getElem?_append_right hle, hx, Nat.sub_self, hy]
        all_goals simp
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        by_cases hj : j < ps.length
        · have := hIJ j (by simp; omega)
          simp only [uncptPermTuple, hj, if_true] at this
          have hj' : j < (coords (fst (ns := ps) (ms := [c]) I)).length := by omega
          rw [this, hcI, List.getElem?_append_left hj', hy]
          all_goals simp
        · have h1 : (coords J).length ≤ j + 1 := by omega
          have h2 : (coords (snd (ns := ps) (ms := [c]) I) ++
              coords (fst (ns := ps) (ms := [c]) I)).length ≤ j + 1 := by
            rw [List.length_append, hx]
            show 1 + ps.length ≤ j + 1
            omega
          rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]
    rw [hJ]
    conv_lhs => rw [hI]
    rw [get_kernelToCpt]

/-! ## Normalisation -/

/-- **A CPT normalised over its last axis gives a normalised kernel, and conversely.** -/
theorem normalised_cptToKernel_iff {ps : List ℕ} {c : ℕ} (A : CptTable ℝ ps c) :
    Finite.Kernel.Normalised (KernelTable.toFiniteKernel (cptToKernel A)) ↔
      ∀ x, ∑ i : Fin c, A.entry x i = 1 := by
  have hsum : ∀ x, ∑ y : MIdx [c], KernelTable.toFiniteKernel (cptToKernel A) x y =
      ∑ i : Fin c, A.entry x i := by
    intro x
    let e : MIdx [c] ≃ Fin c :=
      { toFun := head, invFun := childIdx, left_inv := childIdx_head, right_inv := fun _ => rfl }
    refine Fintype.sum_equiv e _ (fun i => A.entry x i) fun y => ?_
    exact toKernel_cptToKernel A x (head y)
  simp only [Finite.Kernel.Normalised, hsum]

end FiniteKernelsProofs.Layout
