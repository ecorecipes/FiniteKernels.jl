import FiniteKernelsProofs

/-! Axiom audit for the default target (`Roadmap.lean` is deliberately not imported).
Every line should report at most `propext`, `Classical.choice`, `Quot.sound`. -/

open FiniteKernelsProofs.Finite.Kernel

#print axioms FiniteKernelsProofs.smoke

-- Finite/Kernel.lean: preservation, category, monoidal, comonoid laws
#print axioms Normalised.comp
#print axioms Normalised.tensor
#print axioms Stochastic.comp
#print axioms Stochastic.tensor
#print axioms Normalised.idK
#print axioms Normalised.copy
#print axioms Normalised.discard
#print axioms Normalised.swap
#print axioms Normalised.pointMass
#print axioms comp_assoc
#print axioms idK_comp
#print axioms comp_idK
#print axioms comp_tensor
#print axioms tensor_idK
#print axioms tensor_assoc
#print axioms tensor_unit_left
#print axioms tensor_unit_right
#print axioms swap_swap
#print axioms tensor_swap
#print axioms hexagon
#print axioms copy_assoc
#print axioms copy_discard_left
#print axioms copy_discard_right
#print axioms copy_discard_left_strict
#print axioms copy_discard_right_strict
#print axioms copy_swap
#print axioms copy_prod
#print axioms discard_prod
#print axioms copy_unit
#print axioms discard_unit
#print axioms ofFun_copy_natural
#print axioms ofFun_discard_natural

-- Finite/Laws.lean: the two Julia-pinned characterisations
#print axioms comp_discard_eq_discard_iff
#print axioms Normalised.comp_discard
#print axioms Normalised.state_discard
#print axioms exists_pointMass_of_mul
#print axioms comp_copy_eq_iff_isDeterministic
#print axioms isDeterministic_iff_exists_ofFun
#print axioms comp_copy_eq_tensor_iff_isPointMass
#print axioms comp_copy_eq_tensor_iff_isPointMass'
#print axioms pointMass_comp_copy
