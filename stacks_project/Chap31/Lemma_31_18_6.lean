module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.FlatLocus
import StacksCheckRecall

/-!
# Lemma 31.18.6

A flat open neighborhood of a relative effective Cartier divisor.

@stack 062V
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 31.18.6
A locally finitely presented morphism is flat on an open neighborhood of the support of a
relative effective Cartier divisor.
-/
@[stacks 062V] #check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.exists_flat_openContaining_support_of_locallyOfFinitePresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (D : X.IdealSheafData)
      [AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D]
      [AlgebraicGeometry.LocallyOfFinitePresentation f],
      ∃ U : X.Opens, (D.support : Set X) ⊆ (U : Set X) ∧
        AlgebraicGeometry.Flat (U.ι ≫ f))
