import FiniteKernelsProofs.Layout.ColumnMajor

/-!
# The stride-based product of two factors

`multiply(f, g)` in `BayesianNetworkInference.jl` (`src/factors.jl`) builds the product over the
union of the two scopes without permuting either table:

* `_union_axes` lists the result axes (`f`'s variables, then `g`'s new ones); a factor's axis
  `j` is the result axis `pa[j]`, so its table has shape `pa.map ns.get`;
* `_result_strides(h, vars)` gives each result axis the column-major stride that `h`'s own table
  has for that variable, and `0` if `h` lacks it (`resultStride`, `resultStride_eq`);
* `_product_into!` walks the result's joint states in column-major order with an odometer,
  updating the two table offsets incrementally (`bump`, `productLoop`), and stores
  `out[i] = a[ai] * b[bi]`.

Here a factor over result positions `pa` is, semantically, the function
`I ↦ F.get (project I pa)` of the joint multi-index (it reads the coordinates of its own axes),
and the **named product** is the pointwise product of those functions (`namedProduct`).

* `offset_eq_lin`: for a factor without repeated variables (`pa.Nodup`, which the `Factor`
  constructor enforces), the result-stride offset `∑ₖ Iₖ * resultStride k` is the position of
  the projected multi-index in the factor's own table.
* `slotOffset_eq_lin`: the per-slot strides of `BayesianNetworks`' `_Factor` (one stride per
  table axis, repeats allowed) compute the same position with no `Nodup` hypothesis, and
  `resultStride_repeated` shows that the result-stride form is wrong for repeated axes.
* `bump_spec` and `productLoop_eq`: the odometer step moves to `MIdx.next` and keeps each offset
  equal to its stride sum.
* `productInto_getElem?` / `productInto_eq`: **the list written by the loop is the flat
  column-major table of the named product**, including the zero-dimensional case (one entry).

Values live in any type with a multiplication (a semiring in practice); this is exact index
arithmetic, not a statement about Julia execution or IEEE rounding.
-/

namespace FiniteKernelsProofs.Layout

open MIdx

/-! ## Coordinates and projections -/

/-- The coordinate of axis `k`, as an element of that axis. -/
def MIdx.coord : {ns : List ℕ} → MIdx ns → (k : Fin ns.length) → Fin (ns.get k)
  | [], _, k => k.elim0
  | _ :: _, idx, ⟨0, _⟩ => head idx
  | _ :: _, idx, ⟨k + 1, h⟩ => coord (tail idx) ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- All coordinates of a multi-index at linear position zero are zero. -/
theorem MIdx.coord_eq_zero_of_lin : {ns : List ℕ} → (z : MIdx ns) → lin z = 0 →
    ∀ k, (coord z k : ℕ) = 0
  | [], _, _, k => k.elim0
  | n :: _, z, h, ⟨0, _⟩ => by
    have h' : (head z : ℕ) + n * lin (tail z) = 0 := h
    show (head z : ℕ) = 0
    omega
  | n :: _, z, h, ⟨k + 1, hk⟩ => by
    have h' : (head z : ℕ) + n * lin (tail z) = 0 := h
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (head z).isLt
    have ht : lin (tail z) = 0 := by
      rcases Nat.mul_eq_zero.1 (by omega : n * lin (tail z) = 0) with h'' | h''
      · omega
      · exact h''
    exact coord_eq_zero_of_lin (tail z) ht ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- The multi-index of a factor whose axis `j` is the result axis `pa[j]`: `I[pa]`. -/
def project {ns : List ℕ} (I : MIdx ns) : (pa : List (Fin ns.length)) → MIdx (pa.map ns.get)
  | [] => nil
  | p :: pa => cons (coord I p) (project I pa)

variable {α : Type} {ns : List ℕ}

/-- The named (functional) product: at every joint multi-index, the product of the two
factors' entries at their projected multi-indices. -/
def namedProduct [Mul α] (pa pb : List (Fin ns.length)) (F : Tensor α (pa.map ns.get))
    (G : Tensor α (pb.map ns.get)) : Tensor α ns :=
  Tensor.ofFun fun I => F.get (project I pa) * G.get (project I pb)

/-! ## Strides -/

/-- `_result_strides(h, vars)`, recursively: the first slot has stride one and every later slot
the size of the earlier ones times its stride in the tail. -/
def resultStride (ns : List ℕ) : List (Fin ns.length) → Fin ns.length → ℕ
  | [], _ => 0
  | p :: pa, i => if i = p then 1 else ns.get p * resultStride ns pa i

/-- `resultStride` is literally `_result_strides`: the column-major stride of the **first**
slot of the factor that carries result axis `i`, and `0` when there is none. -/
theorem resultStride_eq (pa : List (Fin ns.length)) (i : Fin ns.length) :
    resultStride ns pa i = if i ∈ pa then ((pa.map ns.get).take (pa.idxOf i)).prod else 0 := by
  induction pa with
  | nil => simp [resultStride]
  | cons p pa ih =>
    by_cases h : i = p
    · subst h
      simp [resultStride]
    · have hne : p ≠ i := Ne.symm h
      simp only [resultStride, h, if_false, ih, List.mem_cons, false_or, List.map_cons,
        List.idxOf_cons_ne _ hne, Nat.succ_eq_add_one, List.take_succ_cons, List.prod_cons]
      split_ifs <;> simp

theorem resultStride_of_notMem (pa : List (Fin ns.length)) (i : Fin ns.length) (h : i ∉ pa) :
    resultStride ns pa i = 0 := by
  rw [resultStride_eq, if_neg h]

/-- The table offset `∑ₖ Iₖ * resultStride k` of the result multi-index `I`. -/
def offset (pa : List (Fin ns.length)) (I : MIdx ns) : ℕ :=
  ∑ k : Fin ns.length, (coord I k : ℕ) * resultStride ns pa k

/-- **Result strides locate the projected entry** when the factor has no repeated variable. -/
theorem offset_eq_lin (pa : List (Fin ns.length)) (hpa : pa.Nodup) (I : MIdx ns) :
    offset pa I = lin (project I pa) := by
  induction pa with
  | nil => simp [offset, resultStride, project]
  | cons p pa ih =>
    obtain ⟨hp, hpa⟩ := List.nodup_cons.1 hpa
    have hterm : ∀ k : Fin ns.length, (coord I k : ℕ) * resultStride ns (p :: pa) k =
        (if k = p then (coord I k : ℕ) else 0) +
          ns.get p * ((coord I k : ℕ) * resultStride ns pa k) := by
      intro k
      by_cases hk : k = p
      · rw [hk]
        simp [resultStride, resultStride_of_notMem pa p hp]
      · simp only [resultStride, hk, if_false, zero_add]
        ring
    unfold offset
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.mul_sum]
    rw [show (∑ k : Fin ns.length, (coord I k : ℕ) * resultStride ns pa k) = offset pa I from rfl,
      ih hpa]
    rfl

theorem coords_project (I : MIdx ns) (pa : List (Fin ns.length)) :
    coords (project I pa) = pa.map fun p => (coord I p : ℕ) := by
  induction pa with
  | nil => rfl
  | cons p pa ih =>
    show (coord I p : ℕ) :: coords (project I pa) = _
    rw [ih]
    rfl

/-- **Per-slot strides** (`BayesianNetworks`' `_Factor`: `idx += strides[j] * (ci[axes[j]] - 1)`)
locate the projected entry for every slot list, repeated result axes included. -/
theorem slotOffset_eq_lin (pa : List (Fin ns.length)) (I : MIdx ns) :
    lin (project I pa) = ∑ j ∈ Finset.range (pa.map ns.get).length,
      (coords (project I pa)).getD j 0 * stride (pa.map ns.get) j :=
  lin_eq_sum_stride _

/-- With a repeated axis the result-stride form reads the wrong entry: for one result axis of
size two and a factor carrying it twice (the diagonal of a `2 × 2` table), the result-stride
offset of state `1` is `1`, but the diagonal entry `(1, 1)` sits at position `3`. -/
theorem resultStride_repeated :
    offset (ns := [2]) [⟨0, by decide⟩, ⟨0, by decide⟩] (cons ⟨1, by decide⟩ nil) = 1 ∧
      lin (project (ns := [2]) (cons ⟨1, by decide⟩ nil) [⟨0, by decide⟩, ⟨0, by decide⟩]) = 3 := by
  decide

/-! ## The odometer loop of `_product_into!` -/

/-- `∑ₖ posₖ * sₖ` over two lists. -/
def dot (pos : List ℕ) (s : List ℤ) : ℤ := (List.zipWith (fun p t => (p : ℤ) * t) pos s).sum

/-- One pass of the inner `for k in 1:d` loop, for one table offset:
`pos[k] += 1; off += s[k]; pos[k] < sz[k] && break; pos[k] = 0; off -= s[k] * sz[k]`. -/
def bump : List ℕ → List ℕ → List ℤ → ℤ → List ℕ × ℤ
  | n :: sz, p :: pos, t :: s, off =>
    if p + 1 < n then ((p + 1) :: pos, off + t)
    else
      let r := bump sz pos s (off + t - t * n)
      (0 :: r.1, r.2)
  | _, pos, _, off => (pos, off)

theorem dot_cons (p : ℕ) (pos : List ℕ) (t : ℤ) (s : List ℤ) :
    dot (p :: pos) (t :: s) = p * t + dot pos s := by
  simp [dot]

/-- **The odometer step**: from the coordinates of `idx` and an offset equal to its stride sum
(plus any constant), `bump` reaches the coordinates of `next idx` and its stride sum. -/
theorem bump_spec : {sz : List ℕ} → (idx : MIdx sz) → (s : List ℤ) → s.length = sz.length →
    (off : ℤ) → bump sz (coords idx) s (off + dot (coords idx) s) =
      (coords (next idx), off + dot (coords (next idx)) s)
  | [], idx, s, _, off => by
    simp [bump, coords]
  | n :: sz, idx, [], hs, _ => by simp at hs
  | n :: sz, idx, t :: s, hs, off => by
    have hs' : s.length = sz.length := by simpa using hs
    have hi := (head idx).isLt
    rw [show idx = cons (head idx) (tail idx) from rfl]
    simp only [coords_cons, dot_cons, bump]
    by_cases h : (head idx : ℕ) + 1 < n
    · rw [if_pos h]
      simp only [next, head_cons, tail_cons, h, dite_true, coords_cons, dot_cons,
        Prod.mk.injEq, true_and]
      push_cast
      ring
    · rw [if_neg h]
      have he : (head idx : ℕ) + 1 = n := by omega
      have hoff : off + ((head idx : ℕ) * t + dot (coords (tail idx)) s) + t - t * n =
          off + dot (coords (tail idx)) s := by
        have hn : (n : ℤ) = ((head idx : ℕ) : ℤ) + 1 := by exact_mod_cast he.symm
        rw [hn]
        ring
      simp only [hoff, bump_spec (tail idx) s hs' off, next, head_cons, tail_cons, h,
        dite_false, coords_cons, dot_cons, Nat.cast_zero, zero_mul, zero_add]

/-- The loop of `_product_into!`: write `a[ai] * b[bi]`, then advance the shared odometer and
both offsets. -/
def productLoop [Mul α] (sz : List ℕ) (as bs : List ℤ) (a b : ℕ → α) :
    ℕ → List ℕ → ℤ → ℤ → List α
  | 0, _, _, _ => []
  | k + 1, pos, ai, bi =>
    (a ai.toNat * b bi.toNat) ::
      productLoop sz as bs a b k (bump sz pos as ai).1 (bump sz pos as ai).2 (bump sz pos bs bi).2

theorem productLoop_eq [Mul α] (sz : List ℕ) (as bs : List ℤ) (has : as.length = sz.length)
    (hbs : bs.length = sz.length) (a b : ℕ → α) (k : ℕ) (idx : MIdx sz) :
    productLoop sz as bs a b k (coords idx) (dot (coords idx) as) (dot (coords idx) bs) =
      (List.range k).map fun j =>
        a (dot (coords (next^[j] idx)) as).toNat * b (dot (coords (next^[j] idx)) bs).toNat := by
  induction k generalizing idx with
  | zero => rfl
  | succ k ih =>
    have ha := bump_spec idx as has 0
    have hb := bump_spec idx bs hbs 0
    simp only [zero_add] at ha hb
    simp only [productLoop, ha, hb]
    rw [ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

/-- The coordinates of the all-zero multi-index. -/
theorem coords_of_lin_eq_zero : {sz : List ℕ} → (z : MIdx sz) → lin z = 0 →
    coords z = List.replicate sz.length 0
  | [], _, _ => rfl
  | n :: sz, z, h => by
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (head z).isLt
    rw [show z = cons (head z) (tail z) from rfl] at h ⊢
    simp only [lin_cons] at h
    have h0 : (head z : ℕ) = 0 := by omega
    have ht : lin (tail z) = 0 := by
      rcases Nat.mul_eq_zero.1 (by omega : n * lin (tail z) = 0) with h' | h'
      · omega
      · exact h'
    rw [coords_cons, h0, coords_of_lin_eq_zero (tail z) ht]
    rfl

/-- `_product_into!(out, sz, a, as, b, bs)` with `pos = zeros`, `ai = bi = 1` (0-based here). -/
def productInto [Mul α] (sz : List ℕ) (as bs : List ℤ) (a b : ℕ → α) : List α :=
  productLoop sz as bs a b sz.prod (List.replicate sz.length 0) 0 0

theorem dot_ofFn {sz : List ℕ} (I : MIdx sz) (f : Fin sz.length → ℕ) :
    dot (coords I) (List.ofFn fun k => (f k : ℤ)) = ((∑ k, (coord I k : ℕ) * f k : ℕ) : ℤ) := by
  induction sz with
  | nil => simp [dot, coords]
  | cons n sz ih =>
    rw [show I = cons (head I) (tail I) from rfl, List.ofFn_succ, coords_cons, dot_cons]
    show _ = ((∑ k : Fin (sz.length + 1), (coord (cons (head I) (tail I)) k : ℕ) * f k : ℕ) : ℤ)
    rw [Fin.sum_univ_succ, ih (tail I) (fun k => f k.succ)]
    push_cast
    rfl

/-- The result strides of a factor as the integer vector the loop uses. -/
def strides (ns : List ℕ) (pa : List (Fin ns.length)) : List ℤ :=
  List.ofFn fun k => (resultStride ns pa k : ℤ)

theorem dot_strides (pa : List (Fin ns.length)) (hpa : pa.Nodup) (I : MIdx ns) :
    dot (coords I) (strides ns pa) = lin (project I pa) := by
  rw [strides, dot_ofFn, show (∑ k, (coord I k : ℕ) * resultStride ns pa k) = offset pa I
    from rfl, offset_eq_lin pa hpa]

/-- The projection of the all-zero multi-index has linear position zero. -/
theorem lin_project_zero (z : MIdx ns) (hz : lin z = 0) (pa : List (Fin ns.length)) :
    lin (project z pa) = 0 := by
  induction pa with
  | nil => rfl
  | cons p pa ih =>
    show (coord z p : ℕ) + ns.get p * lin (project z pa) = 0
    rw [coord_eq_zero_of_lin z hz p, ih, mul_zero, add_zero]

theorem get_eq_lin (A : Tensor α ns) (idx : MIdx ns) : A.get idx = A ⟨lin idx, lin_lt idx⟩ := by
  unfold Tensor.get
  congr 1
  exact Fin.ext (toFlat_val idx)

theorem length_productLoop [Mul α] (sz : List ℕ) (as bs : List ℤ) (a b : ℕ → α) (k : ℕ)
    (pos : List ℕ) (ai bi : ℤ) : (productLoop sz as bs a b k pos ai bi).length = k := by
  induction k generalizing pos ai bi with
  | zero => rfl
  | succ k ih => simp [productLoop, ih]

/-- **The stride-based product computes the named product, entry by entry.** For factors
without repeated variables whose flat tables `a`, `b` store `F`, `G` column-major, the entry
that `_product_into!` writes at the column-major position of the joint multi-index `I` is
`F[I[pa]] * G[I[pb]]`. -/
theorem productInto_getElem? [Mul α] (pa pb : List (Fin ns.length)) (hpa : pa.Nodup)
    (hpb : pb.Nodup) (F : Tensor α (pa.map ns.get)) (G : Tensor α (pb.map ns.get))
    (a b : ℕ → α) (ha : ∀ J, a (lin J) = F.get J) (hb : ∀ J, b (lin J) = G.get J)
    (I : MIdx ns) :
    (productInto ns (strides ns pa) (strides ns pb) a b)[lin I]? =
      some ((namedProduct pa pb F G).get I) := by
  have hpos : 0 < ns.prod := lt_of_le_of_lt (Nat.zero_le _) (lin_lt I)
  obtain ⟨z, hz⟩ := lin_surjective (ns := ns) 0 hpos
  have hlen : ∀ pa : List (Fin ns.length), (strides ns pa).length = ns.length := by
    intro pa; simp [strides]
  have hstart : productInto ns (strides ns pa) (strides ns pb) a b =
      productLoop ns (strides ns pa) (strides ns pb) a b ns.prod (coords z)
        (dot (coords z) (strides ns pa)) (dot (coords z) (strides ns pb)) := by
    rw [dot_strides pa hpa, dot_strides pb hpb, lin_project_zero z hz, lin_project_zero z hz,
      coords_of_lin_eq_zero z hz]
    all_goals rfl
  rw [hstart, productLoop_eq _ _ _ (hlen pa) (hlen pb), List.getElem?_map,
    List.getElem?_range (lin_lt I), Option.map_some]
  refine congrArg some ?_
  show a (dot (coords (next^[lin I] z)) (strides ns pa)).toNat *
      b (dot (coords (next^[lin I] z)) (strides ns pb)).toNat = _
  have hiter : next^[lin I] z = I := by
    apply lin_injective
    rw [lin_iterate_next z hz, Nat.mod_eq_of_lt (lin_lt I)]
  rw [hiter, dot_strides pa hpa, dot_strides pb hpb, Int.toNat_natCast, Int.toNat_natCast, ha, hb,
    namedProduct, Tensor.get_ofFun]

/-- **The loop output is the flat column-major table of the named product.** -/
theorem productInto_eq [Mul α] (pa pb : List (Fin ns.length)) (hpa : pa.Nodup)
    (hpb : pb.Nodup) (F : Tensor α (pa.map ns.get)) (G : Tensor α (pb.map ns.get))
    (a b : ℕ → α) (ha : ∀ J, a (lin J) = F.get J) (hb : ∀ J, b (lin J) = G.get J) :
    productInto ns (strides ns pa) (strides ns pb) a b =
      List.ofFn (namedProduct pa pb F G) := by
  apply List.ext_getElem?
  intro p
  by_cases hp : p < ns.prod
  · obtain ⟨I, rfl⟩ := lin_surjective (ns := ns) p hp
    rw [productInto_getElem? pa pb hpa hpb F G a b ha hb I, List.getElem?_ofFn,
      dif_pos (lin_lt I), get_eq_lin]
  · have h1 : (productInto ns (strides ns pa) (strides ns pb) a b).length ≤ p := by
      rw [productInto, length_productLoop]
      omega
    have h2 : (List.ofFn (namedProduct pa pb F G)).length ≤ p := by
      rw [List.length_ofFn]
      omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

end FiniteKernelsProofs.Layout
