/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Galois.IntegralClosure.Tower.Tame
import StacksCheckRecall

@[expose] public section

/-!
# Remark 15.113.11

@stack 0BU8

The finite and tower APIs for the tame/wild factorization are canonical ReasLib owners.  This
remark is therefore a source-facing recall block; it deliberately introduces no chapter aliases,
local algebra structures, or chosen inverses.
-/

namespace Remark_15_113_11

/- Remark 15.113.11 (1): the tame inertia order divides the ramification index. -/
@[stacks 0BU8 "Remark 15.113.11 (1): tame inertia order divisor"]
#check (@integralClosure.Tame.tameInertiaCard_dvd_ramificationIdx)

/- Remark 15.113.11 (2): the ramification index is the wild scale times the tame order. -/
@[stacks 0BU8 "Remark 15.113.11 (2): tame/wild ramification factorization"]
#check (@integralClosure.Tame.ramificationIdxIn_eq_tameScale_mul_tameCard)

/- Remark 15.113.11 (3): the wild scale has the residue-characteristic alternatives. -/
@[stacks 0BU8 "Remark 15.113.11 (3): wild scale arithmetic"]
#check (@integralClosure.Tame.tameScale_spec)

/- Remark 15.113.11 (4): roots indexed by the ramification index equal tame roots. -/
@[stacks 0BU8 "Remark 15.113.11 (4): roots of unity scale identification"]
#check (@integralClosure.Tame.rootsOfUnity_eq_tameCard)

/- Remark 15.113.11 (5): the canonical scaled tame inertia character. -/
@[stacks 0BU8 "Remark 15.113.11 (5): scaled tame inertia character"]
#check (@integralClosure.Tame.scaledCharacter)

/- Remark 15.113.11 (6): the scaled character is the wild-scale power of the original character. -/
@[stacks 0BU8 "Remark 15.113.11 (6): scaled character power formula"]
#check (@integralClosure.Tame.scaledCharacter_coe_apply)

/- Remark 15.113.11 (7): the explicit forward map on the tame quotient. -/
@[stacks 0BU8 "Remark 15.113.11 (7): scaled tame quotient forward map"]
#check (@integralClosure.Tame.scaledQuotientMap)

/- Remark 15.113.11 (8): the forward map agrees with the scaled character on quotient classes. -/
@[stacks 0BU8 "Remark 15.113.11 (8): scaled quotient class formula"]
#check (@integralClosure.Tame.scaledQuotientMap_mk)

/- Remark 15.113.11 (9): the scaled quotient map is bijective. -/
@[stacks 0BU8 "Remark 15.113.11 (9): scaled tame quotient bijection"]
#check (@integralClosure.Tame.scaledQuotientMap_bijective)

/- Remark 15.113.11 (10): the scaled character has wild inertia as its kernel. -/
@[stacks 0BU8 "Remark 15.113.11 (10): scaled tame character kernel"]
#check (@integralClosure.Tame.scaledCharacter_ker)

/- Remark 15.113.11 (11): the scaled character is surjective. -/
@[stacks 0BU8 "Remark 15.113.11 (11): scaled tame character surjectivity"]
#check (@integralClosure.Tame.scaledCharacter_surjective)

/- Remark 15.113.11 (12): decomposition-group conjugation is compatible with the scaled character. -/
@[stacks 0BU8 "Remark 15.113.11 (12): scaled tame character conjugation"]
#check (@integralClosure.Tame.scaledCharacter_conj_compatible)

/- Remark 15.113.11 (13): restriction and the scaled character form the canonical tower square. -/
@[stacks 0BU8 "Remark 15.113.11 (13): scaled tame character tower compatibility"]
#check (@integralClosure.Tower.Tame.scaledCharacter_naturality)

/- Remark 15.113.11 (14): pointwise form of the canonical tower square. -/
@[stacks 0BU8 "Remark 15.113.11 (14): pointwise scaled tame character compatibility"]
#check (@integralClosure.Tower.Tame.scaledCharacter_naturality_apply)

end Remark_15_113_11
