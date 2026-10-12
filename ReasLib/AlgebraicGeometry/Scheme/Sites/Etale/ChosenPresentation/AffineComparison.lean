/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation.Affine
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale

/-!
# Comparison of chosen big affine and big étale sites

The inclusion of the affine objects in a chosen big étale slice is special
cocontinuous. Its cocontinuous direct image therefore induces an equivalence
on sheaves of types.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigEtaleSite.AffineComparison

/-- The inclusion from the affine objects of a chosen big étale slice to the
whole slice is special cocontinuous. -/
theorem isSpecialCocontinuous (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    (bigAffineInclusion X S).IsSpecialCocontinuous
      (bigAffineTopology X S) (bigTopology X S) := sorry

/-- The affine inclusion in a chosen big étale slice carries its canonical
special-cocontinuity instance. -/
instance inclusionIsSpecialCocontinuous
    (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    (bigAffineInclusion X S).IsSpecialCocontinuous
      (bigAffineTopology X S) (bigTopology X S) :=
  isSpecialCocontinuous X S

/-- The cocontinuous direct image from the chosen big affine étale site to the
chosen big étale slice is an equivalence on sheaves of types. -/
noncomputable instance directImageIsEquivalence
    (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    ((bigAffineInclusion X S).sheafPushforwardCocontinuous (Type (max u v))
      (bigAffineTopology X S) (bigTopology X S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence
    (bigAffineInclusion X S)

end AlgebraicGeometry.ChosenBigEtaleSite.AffineComparison
