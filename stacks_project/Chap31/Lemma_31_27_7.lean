module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Picard
import StacksCheckRecall

/-!
# Lemma 31.27.7

Locally factorial schemes are exactly the normal schemes for which the comparison from the Picard
group to the Weil divisor class group is surjective.

@stack 0BE9
-/

@[expose] public section

universe u

/- Lemma 31.27.7: locally factorial schemes are normal and have surjective
Picard-to-Weil-class-group comparison. -/
@[stacks 0BE9] #check
  (AlgebraicGeometry.Scheme.PicardComparison.normalAndSurjective :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X],
      (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) →
        X.isNormal ∧ Function.Surjective
          (AlgebraicGeometry.Scheme.picardToWeilDivisorClassGroup X))

/- Normal schemes with surjective Picard-to-Weil-class-group comparison are locally factorial. -/
#check
  (AlgebraicGeometry.Scheme.PicardComparison.locallyFactorial :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X],
      X.isNormal →
        Function.Surjective (AlgebraicGeometry.Scheme.picardToWeilDivisorClassGroup X) →
          ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))

/- On a locally factorial scheme, the Picard-to-Weil-class-group comparison is bijective. -/
#check
  (AlgebraicGeometry.Scheme.PicardComparison.bijective :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X],
      (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) →
        Function.Bijective (AlgebraicGeometry.Scheme.picardToWeilDivisorClassGroup X))
