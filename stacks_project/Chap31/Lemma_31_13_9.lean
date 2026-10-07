module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Factors
import StacksCheckRecall

/-!
# Lemma 31.13.9

Effective Cartier factors of a divisor sum.

@stack 07ZV
-/

@[expose] public section

universe u

/- Lemma 31.13.9

If an effective Cartier divisor has ideal sheaf equal to a product, then the left factor defines
an effective Cartier divisor.
-/
@[stacks 07ZV] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.isEffectiveCartierDivisor_left_of_mul :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (D Z Y : X.IdealSheafData),
      D.ideal = (fun U : X.affineOpens ↦ Z.ideal U * Y.ideal U) →
        AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι →
          AlgebraicGeometry.IsEffectiveCartierDivisor Z.subschemeι)

#check
  (AlgebraicGeometry.Scheme.IdealSheafData.isEffectiveCartierDivisor_right_of_mul :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (D Z Y : X.IdealSheafData),
      D.ideal = (fun U : X.affineOpens ↦ Z.ideal U * Y.ideal U) →
        AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι →
          AlgebraicGeometry.IsEffectiveCartierDivisor Y.subschemeι)

#check (AlgebraicGeometry.eq_effectiveCartierDivisorSum_of_ideal_eq_mul :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (D Z Y : X.IdealSheafData),
    D.ideal = (fun U : X.affineOpens ↦ Z.ideal U * Y.ideal U) →
      D = AlgebraicGeometry.effectiveCartierDivisorSum Z Y)
