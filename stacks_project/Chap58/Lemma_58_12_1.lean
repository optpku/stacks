/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.ResidueField.IsAlgClosed
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 58.12.1 -/
@[stacks 0BSP]
#check (Ideal.ResidueField.isAlgClosed_of_isSepClosed_fractionRing :
  (A : Type u) → [CommRing A] → [IsDomain A] →
    (K : Type v) → [Field K] → [Algebra A K] → [IsFractionRing A K] →
      [IsIntegrallyClosedIn A K] → [IsSepClosed K] →
        (p : Ideal A) → [p.IsPrime] → p ≠ ⊥ →
          IsAlgClosed p.ResidueField)
