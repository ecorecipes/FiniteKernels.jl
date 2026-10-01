import FiniteKernelsProofs.Layout.KernelLayout

/-!
# SA-Pass shadow module: `cpt` is an entry-preserving bijection of layouts

Claim `fk.cpt-layout`, from `Layout.cptToKernel_permutedims`, `Layout.cptEquiv` and
`Layout.toKernel_cptToKernel`:
"`cptToKernel_permutedims`, `cptEquiv` and `toKernel_cptToKernel` prove that `cpt`'s
`permutedims(table, (n + 1, 1, …, n))` is a bijection between the `(parents..., child)` and
outputs-first layouts that preserves every entry: the kernel's `P(child = i | parents = x)` is
the CPT entry `table[x..., i]`."
-/

namespace FiniteKernelsProofs.Shadows.CptLayout

open FiniteKernelsProofs.Layout FiniteKernelsProofs.Layout.MIdx

/-- The three cited results, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (α : Type) (ps : List ℕ) (c : ℕ),
    (∀ A : CptTable α ps c, PermutedimsSpec (cptPermTuple ps.length) A (cptToKernel A)) ∧
    Function.Bijective (cptToKernel (α := α) (ps := ps) (c := c)) ∧
    ∀ (A : CptTable α ps c) (x : MIdx ps) (i : Fin c),
      KernelTable.toKernel (cptToKernel A) x (childIdx i) = A.entry x i

/-- "`cpt`'s `permutedims(table, (n + 1, 1, …, n))`": the conversion meets Julia's
`permutedims` contract for that tuple. -/
abbrev Shadow1 : Prop :=
  ∀ (α : Type) (ps : List ℕ) (c : ℕ) (A : CptTable α ps c),
    PermutedimsSpec (cptPermTuple ps.length) A (cptToKernel A)

/-- "a bijection between the `(parents..., child)` and outputs-first layouts". -/
abbrev Shadow2 : Prop :=
  ∀ (α : Type) (ps : List ℕ) (c : ℕ),
    Function.Bijective (cptToKernel (α := α) (ps := ps) (c := c))

/-- "preserves every entry: … `P(child = i | parents = x)` is the CPT entry `table[x..., i]`". -/
abbrev Shadow3 : Prop :=
  ∀ (α : Type) (ps : List ℕ) (c : ℕ) (A : CptTable α ps c) (x : MIdx ps) (i : Fin c),
    KernelTable.toKernel (cptToKernel A) x (childIdx i) = A.entry x i

theorem forward1 : Candidate → Shadow1 := fun h α ps c => (h α ps c).1

theorem forward2 : Candidate → Shadow2 := fun h α ps c => (h α ps c).2.1

theorem forward3 : Candidate → Shadow3 := fun h α ps c => (h α ps c).2.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate :=
  fun h1 h2 h3 α ps c => ⟨h1 α ps c, h2 α ps c, h3 α ps c⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate := fun α ps c =>
  ⟨FiniteKernelsProofs.Layout.cptToKernel_permutedims,
    (FiniteKernelsProofs.Layout.cptEquiv α ps c).bijective,
    FiniteKernelsProofs.Layout.toKernel_cptToKernel⟩

end FiniteKernelsProofs.Shadows.CptLayout
