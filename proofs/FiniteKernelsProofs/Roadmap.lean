import FiniteKernelsProofs.Theory.FinStoch

/-!
# Roadmap

The two former holes, `MonoidalCategory FinStoch` and `MarkovCategory FinStoch`, are now
proved in `Theory/FinStoch.lean`, imported by the default target and included in the axiom
audit. This compatibility module has no unproved declarations.

Remaining work is a representation bridge to Julia's named axes and floating-point arrays.
The Mathlib instance by itself does not establish that bridge, and no open-network category
or semantic functor is constructed here.
-/

namespace FiniteKernelsProofs.Roadmap

/-- Compatibility name for the finite stochastic category now in the default library. -/
abbrev FinStoch := FiniteKernelsProofs.FinStoch

end FiniteKernelsProofs.Roadmap
