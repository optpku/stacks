/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.FaithfullyFlat.ResidueField
import StacksCheckRecall

/-!
# Lemma 10.39.15
@stack 00HP
-/

@[expose] public section

/- Lemma 10.39.15 [stacks 00HP]: canonical recall of the residue-field fiber
criteria for a flat module.  The tensor/quotient comparison is owned by
`Ideal.ResidueField.nontrivial_tensor_iff`; the faithful-flatness criteria and
the four-clause source presentation are owned by `Module.FaithfullyFlat`. -/
@[stacks 00HP]
#check @Module.FaithfullyFlat.tfae_nontrivial_tensor_residueField

@[stacks 00HP "tensor nontriviality companion"]
#check @Ideal.ResidueField.nontrivial_tensor_iff
@[stacks 00HP "faithful-flat residue-field companion"]
#check @Module.FaithfullyFlat.iff_forall_nontrivial_tensor_residueField
@[stacks 00HP "prime-residue-field companion"]
#check @Module.FaithfullyFlat.iff_forall_nontrivial_tensor_primeResidueField
