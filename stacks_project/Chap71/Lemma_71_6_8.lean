module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Sum.Factors
import StacksCheckRecall

/-!
# Lemma 71.6.8

If the product of the ideal sheaves of two closed subspaces of an algebraic
space cuts out an effective Cartier divisor, then both subspaces are effective
Cartier divisors and the given divisor is their sum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.6.8 (1): if the product of the ideal sheaves of two closed subspaces
of an algebraic space cuts out an effective Cartier divisor, then the left
closed subspace is an effective Cartier divisor. -/
@[stacks 083W] #check
  (AlgebraicGeometry.AlgebraicSpace.isEffectiveCartierDivisor_left_of_mul :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D Z Y : ClosedSubspace X)
      (hD : D.idealSheaf = IdealSubobject.mul Z.idealSheaf Y.idealSheaf)
      [IsEffectiveCartierDivisor D.ι], IsEffectiveCartierDivisor Z.ι)

/- Lemma 71.6.8 (2): if the product of the ideal sheaves of two closed subspaces
of an algebraic space cuts out an effective Cartier divisor, then the right
closed subspace is an effective Cartier divisor. -/
@[stacks 083W] #check
  (AlgebraicGeometry.AlgebraicSpace.isEffectiveCartierDivisor_right_of_mul :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D Z Y : ClosedSubspace X)
      (hD : D.idealSheaf = IdealSubobject.mul Z.idealSheaf Y.idealSheaf)
      [IsEffectiveCartierDivisor D.ι], IsEffectiveCartierDivisor Y.ι)

/- Lemma 71.6.8 (3): if the product of the ideal sheaves of two closed subspaces
of an algebraic space equals the ideal sheaf of `D`, then `D` is isomorphic
over `X` to the sum of the two effective Cartier divisors. -/
@[stacks 083W] #check
  (AlgebraicGeometry.AlgebraicSpace.overIso_effectiveCartierDivisorSum_of_ideal_eq_mul :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D Z Y : ClosedSubspace X)
      (hD : D.idealSheaf = IdealSubobject.mul Z.idealSheaf Y.idealSheaf)
      [IsEffectiveCartierDivisor Z.ι] [IsEffectiveCartierDivisor Y.ι],
      Nonempty (Over.mk D.ι ≅ Over.mk (effectiveCartierDivisorSum Z Y).ι))

/- If the product of the ideal sheaves of two effective Cartier divisors equals
the ideal sheaf of a closed subspace `D`, then `D` has the same ideal sheaf as
the sum of the two divisors. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.idealSheaf_eq_effectiveCartierDivisorSum_of_ideal_eq_mul :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D Z Y : ClosedSubspace X)
      (hD : D.idealSheaf = IdealSubobject.mul Z.idealSheaf Y.idealSheaf)
      [IsEffectiveCartierDivisor Z.ι] [IsEffectiveCartierDivisor Y.ι],
      D.idealSheaf = (effectiveCartierDivisorSum Z Y).idealSheaf)

end AlgebraicGeometry.AlgebraicSpace
