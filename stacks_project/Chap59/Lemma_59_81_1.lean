/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdjoinRoot.Unit
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 59.81.1 -/
@[stacks 0GY2]
#check (AdjoinRoot.existsMonogenicUnitExtension :
  ∀ {A : Type u} [CommRing A] (a b : A), IsCoprime a b →
    IsOfFinOrder (Ideal.Quotient.mk (Ideal.span {b}) a) →
      ∃ (p : Polynomial A) (h_monic : p.Monic),
        Function.Injective (algebraMap A (AdjoinRoot p)) ∧
          IsUnit (algebraMap A (AdjoinRoot p) a -
            algebraMap A (AdjoinRoot p) b * AdjoinRoot.root p))

end
