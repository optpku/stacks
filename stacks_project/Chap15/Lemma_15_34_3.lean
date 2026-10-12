/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.Field.BaseChange

/-!
# Cotangent comparison under a square of fields

This file recalls the canonical comparison maps and their Euler
characteristic.

@stack 07E3
-/

@[expose] public section

/- Lemma 15.34.3 (1), tag `07E3`: the kernel of the
comparison on Kaehler differentials is finite-dimensional. -/
@[stacks 07E3 "Lemma 15.34.3 (1)"]
#check @KaehlerDifferential.finiteDimensional_ker_baseFieldComparison

/- Lemma 15.34.3 (2), tag `07E3`: the cokernel of the
comparison on Kaehler differentials is finite-dimensional. -/
@[stacks 07E3 "Lemma 15.34.3 (2)"]
#check @KaehlerDifferential.finiteDimensional_cokernel_baseFieldComparison

/- Lemma 15.34.3 (3), tag `07E3`: the kernel of the
comparison on first cotangent homology is finite-dimensional. -/
@[stacks 07E3 "Lemma 15.34.3 (3)"]
#check @Algebra.H1Cotangent.finiteDimensional_ker_baseFieldComparison

/- Lemma 15.34.3 (4), tag `07E3`: the cokernel of the
comparison on first cotangent homology is finite-dimensional. -/
@[stacks 07E3 "Lemma 15.34.3 (4)"]
#check @Algebra.H1Cotangent.finiteDimensional_cokernel_baseFieldComparison

/- Lemma 15.34.3 (5), tag `07E3`: the comparison's
Euler characteristic is the difference of the relative transcendence degrees. -/
@[stacks 07E3 "Lemma 15.34.3 (5)"]
#check @Algebra.baseFieldComparison_eulerCharacteristic_eq_trdeg_sub_trdeg
