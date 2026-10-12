/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AbsolutelyFlat.Dimension
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.105.5 (092F)

@stack 092F

The four source conditions are the canonical dimension-theoretic characterizations of an
absolutely flat ring.
-/

/- Lemma 15.105.5: weak dimension at most zero, absolute flatness, reduced Krull dimension zero,
and field-valued prime localizations are equivalent. -/
@[stacks 092F "Lemma 15.105.5"]
#check @IsAbsolutelyFlatRing.tfae

/- Atomic forms of the four-way equivalence. -/
@[stacks 092F "weak dimension zero"]
#check @IsAbsolutelyFlatRing.iff_hasWeakDimensionLE_zero

@[stacks 092F "reduced and zero-dimensional"]
#check @IsAbsolutelyFlatRing.iff_isReduced_and_krullDimLE_zero

@[stacks 092F "prime localizations are fields"]
#check @IsAbsolutelyFlatRing.iff_forall_isField_localizationAtPrime

#check @IsAbsolutelyFlatRing.isReduced
#check @IsAbsolutelyFlatRing.krullDimLE_zero
