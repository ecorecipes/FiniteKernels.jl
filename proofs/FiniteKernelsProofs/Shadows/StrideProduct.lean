import FiniteKernelsProofs.Layout.Product

/-!
# SA-Pass shadow module: the stride-based factor product is the named product

Claim `fk.stride-product`, from `Layout.offset_eq_lin` and `Layout.productInto_getElem?`:
"`offset_eq_lin` proves that `_result_strides` locate each factor's entry at the projected
multi-index when the factor has no repeated variable, and `productInto_getElem?` that the
odometer loop of `multiply` writes, at the column-major position of every joint multi-index, the
product of the two factors' entries at the projected multi-indices."
-/

namespace FiniteKernelsProofs.Shadows.StrideProduct

open FiniteKernelsProofs.Layout FiniteKernelsProofs.Layout.MIdx

/-- The two cited theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (ns : List ℕ) (pa : List (Fin ns.length)), pa.Nodup → ∀ I : MIdx ns,
    offset pa I = lin (project I pa)) ∧
  ∀ (α : Type) [Mul α] (ns : List ℕ) (pa pb : List (Fin ns.length)), pa.Nodup → pb.Nodup →
    ∀ (F : Tensor α (pa.map ns.get)) (G : Tensor α (pb.map ns.get)) (a b : ℕ → α),
      (∀ J, a (lin J) = F.get J) → (∀ J, b (lin J) = G.get J) → ∀ I : MIdx ns,
      (productInto ns (strides ns pa) (strides ns pb) a b)[lin I]? =
        some ((namedProduct pa pb F G).get I)

/-- "`_result_strides` locate each factor's entry at the projected multi-index when the factor
has no repeated variable". -/
abbrev Shadow1 : Prop :=
  ∀ (ns : List ℕ) (pa : List (Fin ns.length)), pa.Nodup → ∀ I : MIdx ns,
    offset pa I = lin (project I pa)

/-- "writes, at the column-major position of every joint multi-index, the product of the two
factors' entries at the projected multi-indices". -/
abbrev Shadow2 : Prop :=
  ∀ (α : Type) [Mul α] (ns : List ℕ) (pa pb : List (Fin ns.length)), pa.Nodup → pb.Nodup →
    ∀ (F : Tensor α (pa.map ns.get)) (G : Tensor α (pb.map ns.get)) (a b : ℕ → α),
      (∀ J, a (lin J) = F.get J) → (∀ J, b (lin J) = G.get J) → ∀ I : MIdx ns,
      (productInto ns (strides ns pa) (strides ns pb) a b)[lin I]? =
        some (F.get (project I pa) * G.get (project I pb))

theorem forward1 : Candidate → Shadow1 := fun h => h.1

theorem forward2 : Candidate → Shadow2 := by
  intro h α _ ns pa pb hpa hpb F G a b ha hb I
  rw [h.2 α ns pa pb hpa hpb F G a b ha hb I, namedProduct, Tensor.get_ofFun]

theorem backward : Shadow1 → Shadow2 → Candidate := by
  refine fun h1 h2 => ⟨h1, ?_⟩
  intro α _ ns pa pb hpa hpb F G a b ha hb I
  rw [h2 α ns pa pb hpa hpb F G a b ha hb I, namedProduct, Tensor.get_ofFun]

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ pa hpa I => FiniteKernelsProofs.Layout.offset_eq_lin pa hpa I,
    fun _ _ _ pa pb hpa hpb F G a b ha hb I =>
      FiniteKernelsProofs.Layout.productInto_getElem? pa pb hpa hpb F G a b ha hb I⟩

end FiniteKernelsProofs.Shadows.StrideProduct
