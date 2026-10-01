import FiniteKernelsProofs.Layout.ColumnMajor

/-!
# SA-Pass shadow module: the column-major linear index

Claim `fk.column-major`, from `Layout.MIdx.linearIndex_bijective` and
`Layout.MIdx.juliaLinearIndex_coords`:
"`linearIndex_bijective` proves that the column-major linear index is a bijection from
multi-indices onto the flat positions `Fin (∏ sizes)`, and `juliaLinearIndex_coords` that
Julia's 1-based `_linear_index` fold computes it plus one."
-/

namespace FiniteKernelsProofs.Shadows.ColumnMajorLayout

open FiniteKernelsProofs.Layout FiniteKernelsProofs.Layout.MIdx

/-- The two cited theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ ns : List ℕ,
    Function.Bijective (fun idx : MIdx ns => (⟨lin idx, lin_lt idx⟩ : Fin ns.prod)) ∧
      ∀ idx : MIdx ns, juliaLinearIndex ns ((coords idx).map (· + 1)) = lin idx + 1

/-- "a bijection": distinct multi-indices have distinct positions. -/
abbrev Shadow1 : Prop := ∀ (ns : List ℕ) (a b : MIdx ns), lin a = lin b → a = b

/-- "onto the flat positions `Fin (∏ sizes)`": every position below the product is hit. -/
abbrev Shadow2 : Prop := ∀ (ns : List ℕ) (p : ℕ), p < ns.prod → ∃ idx : MIdx ns, lin idx = p

/-- "`_linear_index` fold computes it plus one". -/
abbrev Shadow3 : Prop :=
  ∀ (ns : List ℕ) (idx : MIdx ns), juliaLinearIndex ns ((coords idx).map (· + 1)) = lin idx + 1

theorem forward1 : Candidate → Shadow1 := by
  intro h ns a b hab
  exact (h ns).1.1 (Fin.ext hab)

theorem forward2 : Candidate → Shadow2 := by
  intro h ns p hp
  obtain ⟨idx, hidx⟩ := (h ns).1.2 ⟨p, hp⟩
  exact ⟨idx, congrArg Fin.val hidx⟩

theorem forward3 : Candidate → Shadow3 := fun h ns => (h ns).2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := by
  intro h1 h2 h3 ns
  refine ⟨⟨fun a b hab => h1 ns a b (congrArg Fin.val hab), fun p => ?_⟩, h3 ns⟩
  obtain ⟨idx, hidx⟩ := h2 ns p p.isLt
  exact ⟨idx, Fin.ext hidx⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate := fun ns =>
  ⟨FiniteKernelsProofs.Layout.MIdx.linearIndex_bijective ns,
    FiniteKernelsProofs.Layout.MIdx.juliaLinearIndex_coords⟩

end FiniteKernelsProofs.Shadows.ColumnMajorLayout
