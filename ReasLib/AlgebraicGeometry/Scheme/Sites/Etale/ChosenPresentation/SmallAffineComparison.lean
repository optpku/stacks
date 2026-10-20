/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation.Affine
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale

/-!
# Comparison of chosen small affine and small étale sites

The inclusion of the affine objects in a chosen small étale site is special
cocontinuous. Its cocontinuous direct image therefore induces an equivalence
on sheaves of types.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigEtaleSite.SmallAffineComparison

/-- The inclusion from the affine objects of a chosen small étale site to the
whole small site is special cocontinuous. -/
theorem isSpecialCocontinuous (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    (smallAffineInclusion X S).IsSpecialCocontinuous
      (smallAffineTopology X S) (smallTopology X S) := sorry

/-- The affine inclusion in a chosen small étale site carries its canonical
special-cocontinuity instance. -/
instance inclusionIsSpecialCocontinuous
    (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    (smallAffineInclusion X S).IsSpecialCocontinuous
      (smallAffineTopology X S) (smallTopology X S) :=
  isSpecialCocontinuous X S

/-- The cocontinuous direct image from the chosen small affine étale site to
the chosen small étale site is an equivalence on sheaves of types. -/
noncomputable instance directImageIsEquivalence
    (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    ((smallAffineInclusion X S).sheafPushforwardCocontinuous (Type (max u v))
      (smallAffineTopology X S) (smallTopology X S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence
    (smallAffineInclusion X S)

end AlgebraicGeometry.ChosenBigEtaleSite.SmallAffineComparison
