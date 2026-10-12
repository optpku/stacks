/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation.Affine
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Refinement
import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenCovering

/-!
# Comparison of chosen big affine and big h sites

The inclusion of the affine objects in a chosen big h slice is special
cocontinuous. Its cocontinuous direct image therefore induces an equivalence
on sheaves of types.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigHSite.AffineComparison

/-- The inclusion from the affine objects of a chosen big h slice to the whole
slice is special cocontinuous. -/
theorem isSpecialCocontinuous (X : ChosenBigHSite.{u, v}) (S : X.carrier) :
    (ChosenBigSite.affineInclusion X S).IsSpecialCocontinuous
      (bigAffineTopology X S) (bigTopology X S) := sorry

/-- The inclusion from the affine objects of a chosen big h slice to the whole
slice is cocontinuous. -/
theorem isCocontinuous (X : ChosenBigHSite.{u, v}) (S : X.carrier) :
    (ChosenBigSite.affineInclusion X S).IsCocontinuous
      (bigAffineTopology X S) (bigTopology X S) :=
  (isSpecialCocontinuous X S).toIsCocontinuous

/-- The cocontinuous direct image from the chosen big affine h site to the
chosen big h slice is an equivalence on sheaves of types. -/
theorem directImageIsEquivalence
    (X : ChosenBigHSite.{u, v}) (S : X.carrier) :
    (@CategoryTheory.Functor.sheafPushforwardCocontinuous _ _ _ _
      (ChosenBigSite.affineInclusion X S) (Type (max u v)) _
      (bigAffineTopology X S) (bigTopology X S) (isCocontinuous X S)
      inferInstance).IsEquivalence :=
  @CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence
    _ _ _ _ _ _ (ChosenBigSite.affineInclusion X S) (isSpecialCocontinuous X S) inferInstance

end AlgebraicGeometry.ChosenBigHSite.AffineComparison
