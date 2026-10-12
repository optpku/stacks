/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo
import StacksCheckRecall

/-!
# The Beauville-Laszlo Cech sequence

Lemma 15.91.6 identifies exactness of the Beauville-Laszlo Cech sequence with bijectivity of the
map on `f`-power torsion.  Its maps, short complex, glueing-pair predicate, and exactness criteria
are owned by `ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo`.

@stack 0BNR
-/

-- The two explicit maps and their canonical short complex.
@[stacks 0BNR "the left map in the Cech sequence"]
#check @beauvilleLaszloCechLeftMap

@[stacks 0BNR "the right map in the Cech sequence"]
#check @beauvilleLaszloCechRightMap

@[stacks 0BNR "the Beauville-Laszlo Cech sequence"]
#check @beauvilleLaszloCechSequence

-- Lemma 15.91.6: quotient compatibility makes the sequence right exact.
@[stacks 0BNR "Lemma 15.91.6 (1)"]
#check @beauvilleLaszloCechRightMap_surjective_of_principalPowerQuotientMapBijective

-- Lemma 15.91.6: left and middle exactness detect the two halves of torsion-map bijectivity.
@[stacks 0BNR "Lemma 15.91.6 (2)"]
#check @beauvilleLaszloCechLeftMap_injective_iff_fPowerTorsionToExtension_injective

@[stacks 0BNR "Lemma 15.91.6 (3)"]
#check @beauvilleLaszloCechMiddle_exact_iff_fPowerTorsionToExtension_surjective

-- Lemma 15.91.6: the combined glueing-pair criterion and its completion specialization.
@[stacks 0BNR "Lemma 15.91.6"]
#check @isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsionToExtension

@[stacks 0BNR "Lemma 15.91.6, completion specialization"]
#check @principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion
