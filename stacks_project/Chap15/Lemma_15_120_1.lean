/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.K0
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.120.1 (0AFY)

The reusable Euler-characteristic API for this source entry is owned by
`CategoryTheory.EulerCharacteristicMap` and `CochainComplex.eulerCharacteristic` in ReasLib.

@stack 0AFY
-/

/- Lemma 15.120.1: an Euler-characteristic map exists on perfect derived objects. -/
@[stacks 0AFY "Lemma 15.120.1: Euler characteristic map"]
#check @CategoryTheory.exists_eulerCharacteristicMap

/- Lemma 15.120.1 (1): shifting by `n` multiplies the Euler characteristic by
`n.negOnePow`. -/
@[stacks 0AFY "(1), Euler characteristic of a shift"]
#check @CategoryTheory.EulerCharacteristicMap.shift

/- Lemma 15.120.1 (2): the Euler characteristic is additive on distinguished triangles. -/
@[stacks 0AFY "(2), Euler characteristic of a distinguished triangle"]
#check @CategoryTheory.EulerCharacteristicMap.triangle

/- Lemma 15.120.1 (3): a bounded finite-projective representative computes the Euler
characteristic by its alternating sum. -/
@[stacks 0AFY "(3), Euler characteristic of a finite-projective representative"]
#check @CategoryTheory.EulerCharacteristicMap.representative

#check @CategoryTheory.IsEulerCharacteristicValue
#check @CochainComplex.eulerCharacteristic
#check @CochainComplex.eulerCharacteristic_eq_sum_Icc
#check @CochainComplex.eulerCharacteristic_shift

#print axioms CochainComplex.eulerCharacteristic
#print axioms CategoryTheory.exists_eulerCharacteristicMap

end
