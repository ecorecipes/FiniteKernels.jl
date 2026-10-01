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

-- Theory/FinStoch.lean: concrete Mathlib structures and their semantic characterisations
#print axioms FiniteKernelsProofs.FinStoch.instCategory
#print axioms FiniteKernelsProofs.FinStoch.isoOfEquiv
#print axioms FiniteKernelsProofs.FinStoch.instMonoidalCategory
#print axioms FiniteKernelsProofs.FinStoch.instSymmetricCategory
#print axioms FiniteKernelsProofs.FinStoch.instComonObj
#print axioms FiniteKernelsProofs.FinStoch.instIsCommComonObj
#print axioms FiniteKernelsProofs.FinStoch.tensorμ_val
#print axioms FiniteKernelsProofs.FinStoch.instMarkovCategory
#print axioms FiniteKernelsProofs.FinStoch.discard_natural
#print axioms FiniteKernelsProofs.FinStoch.copy_natural_iff
#print axioms FiniteKernelsProofs.FinStoch.no_hom_to_empty

-- Layout/ColumnMajor.lean: column-major storage and its linear index
#print axioms FiniteKernelsProofs.Layout.MIdx.coords_injective
#print axioms FiniteKernelsProofs.Layout.MIdx.appendEquiv
#print axioms FiniteKernelsProofs.Layout.MIdx.coords_append
#print axioms FiniteKernelsProofs.Layout.MIdx.lin_lt
#print axioms FiniteKernelsProofs.Layout.MIdx.lin_eq_sum_stride
#print axioms FiniteKernelsProofs.Layout.MIdx.juliaLinearIndex_coords
#print axioms FiniteKernelsProofs.Layout.MIdx.toFlat
#print axioms FiniteKernelsProofs.Layout.MIdx.toFlat_val
#print axioms FiniteKernelsProofs.Layout.MIdx.lin_injective
#print axioms FiniteKernelsProofs.Layout.MIdx.lin_surjective
#print axioms FiniteKernelsProofs.Layout.MIdx.linearIndex_bijective
#print axioms FiniteKernelsProofs.Layout.MIdx.card
#print axioms FiniteKernelsProofs.Layout.MIdx.lin_append
#print axioms FiniteKernelsProofs.Layout.MIdx.lin_next
#print axioms FiniteKernelsProofs.Layout.MIdx.lin_iterate_next
#print axioms FiniteKernelsProofs.Layout.Tensor.equivFun
#print axioms FiniteKernelsProofs.Layout.Tensor.get_eq_juliaLinearIndex

-- Layout/KernelLayout.lean: outputs-first kernels, the CPT layout and `cpt`
#print axioms FiniteKernelsProofs.Layout.KernelTable.kernelEquiv
#print axioms FiniteKernelsProofs.Layout.KernelTable.kernelMatrix_toFlat
#print axioms FiniteKernelsProofs.Layout.KernelTable.probability_linear
#print axioms FiniteKernelsProofs.Layout.get_cptToKernel
#print axioms FiniteKernelsProofs.Layout.get_kernelToCpt
#print axioms FiniteKernelsProofs.Layout.toKernel_cptToKernel
#print axioms FiniteKernelsProofs.Layout.entry_kernelToCpt
#print axioms FiniteKernelsProofs.Layout.kernelToCpt_cptToKernel
#print axioms FiniteKernelsProofs.Layout.cptToKernel_kernelToCpt
#print axioms FiniteKernelsProofs.Layout.cptEquiv
#print axioms FiniteKernelsProofs.Layout.cptToKernel_apply
#print axioms FiniteKernelsProofs.Layout.coords_eq_of_perm
#print axioms FiniteKernelsProofs.Layout.cptToKernel_permutedims
#print axioms FiniteKernelsProofs.Layout.kernelToCpt_permutedims
#print axioms FiniteKernelsProofs.Layout.normalised_cptToKernel_iff

-- Layout/Product.lean: the stride-based factor product
#print axioms FiniteKernelsProofs.Layout.MIdx.coord_eq_zero_of_lin
#print axioms FiniteKernelsProofs.Layout.get_eq_lin
#print axioms FiniteKernelsProofs.Layout.length_productLoop
#print axioms FiniteKernelsProofs.Layout.resultStride_eq
#print axioms FiniteKernelsProofs.Layout.resultStride_of_notMem
#print axioms FiniteKernelsProofs.Layout.offset_eq_lin
#print axioms FiniteKernelsProofs.Layout.coords_project
#print axioms FiniteKernelsProofs.Layout.slotOffset_eq_lin
#print axioms FiniteKernelsProofs.Layout.resultStride_repeated
#print axioms FiniteKernelsProofs.Layout.bump_spec
#print axioms FiniteKernelsProofs.Layout.productLoop_eq
#print axioms FiniteKernelsProofs.Layout.coords_of_lin_eq_zero
#print axioms FiniteKernelsProofs.Layout.dot_ofFn
#print axioms FiniteKernelsProofs.Layout.dot_strides
#print axioms FiniteKernelsProofs.Layout.lin_project_zero
#print axioms FiniteKernelsProofs.Layout.productInto_getElem?
#print axioms FiniteKernelsProofs.Layout.productInto_eq
