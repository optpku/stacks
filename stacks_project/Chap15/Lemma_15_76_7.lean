/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ResidueField.PrimeFreeModel
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.76.7 (0BCD)

@stack 0BCD

The prime residue-field homology and away minimal-free-model API is owned by
`DerivedCategory.PrimeResidueField`.
-/

@[stacks 0BCD "Prime residue-field homology"]
#check @CategoryTheory.DerivedCategory.PrimeResidueField.homology

@[stacks 0BCD "Lemma 15.76.7 (1)"]
#check @CategoryTheory.DerivedCategory.PrimeResidueField.finiteDimensional_and_finiteSupport

@[stacks 0BCD "Lemma 15.76.7 (2)"]
#check @CategoryTheory.DerivedCategory.PrimeResidueField.existsAwayFreeModel

#print axioms CategoryTheory.DerivedCategory.PrimeResidueField.homology
