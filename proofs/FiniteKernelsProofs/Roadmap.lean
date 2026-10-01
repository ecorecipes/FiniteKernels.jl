import FiniteKernelsProofs.Theory.FinStoch

/-!
# Roadmap

The two former holes, `MonoidalCategory FinStoch` and `MarkovCategory FinStoch`, are now
proved in `Theory/FinStoch.lean`, imported by the default target and included in the axiom
audit. This compatibility module has no unproved declarations.

The layout half of the representation bridge to Julia's arrays is now in the default target:
`Layout/ColumnMajor.lean` (column-major storage; the linear index is a bijection onto
`Fin (∏ sizes)` and equals `_linear_index`), `Layout/KernelLayout.lean` (outputs-first kernel
tables, `kernel_matrix`, `probability`, and the two `cpt` `permutedims` as mutually inverse,
entry-preserving conversions) and `Layout/Product.lean` (the result strides and odometer of
`BayesianNetworkInference.multiply` compute the named product for factors without repeated
variables). Labels (`label_index`) are modelled only as positions.

Remaining: floating-point values and IEEE arithmetic, and any proof that the Julia code executes
these definitions (the correspondence is read off the source). `_broadcastable` is not modelled.
The Mathlib instance by itself does not establish that bridge, and no open-network category
or semantic functor is constructed here.
-/

namespace FiniteKernelsProofs.Roadmap

/-- Compatibility name for the finite stochastic category now in the default library. -/
abbrev FinStoch := FiniteKernelsProofs.FinStoch

end FiniteKernelsProofs.Roadmap
