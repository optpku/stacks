/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.ZeroDimensional
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.61.3

@stack 0ALW
-/

/- Lemma 10.61.3 (Tag 0ALW): recall the reusable finite-type zero-dimensionality criteria. -/
@[stacks 0ALW]
#check @Algebra.FiniteType.zeroDimensionalTFAE

@[stacks 0ALW "finite maximal spectrum criterion"]
#check @Algebra.FiniteType.finiteMaximalSpectrum_iff_krullDimLE_zero

@[stacks 0ALW "infinite maximal spectrum criterion"]
#check @Algebra.FiniteType.infiniteMaximalSpectrum_iff_not_krullDimLE_zero
