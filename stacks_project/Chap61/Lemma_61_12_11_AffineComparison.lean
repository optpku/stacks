module

public import stacks_project.Chap61.Definition_61_12_8_Affine
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous

/-!
# Comparison of chosen big affine and big pro-étale sites

The inclusion of the affine objects in a chosen big pro-étale slice is
special cocontinuous. Its cocontinuous direct image therefore induces an
equivalence on sheaves of types.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite.AffineComparison

/-- The inclusion from the affine objects of a chosen big pro-étale slice to
the whole slice is special cocontinuous. -/
theorem isSpecialCocontinuous (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    (bigAffineInclusion X S).IsSpecialCocontinuous
      (bigAffineTopology X S) (bigTopology X S) := sorry

/-- The affine inclusion in a chosen big pro-étale slice carries its canonical
special-cocontinuity instance. -/
instance inclusionIsSpecialCocontinuous
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    (bigAffineInclusion X S).IsSpecialCocontinuous
      (bigAffineTopology X S) (bigTopology X S) :=
  isSpecialCocontinuous X S

/-- The cocontinuous direct image from the chosen big affine pro-étale site to
the chosen big pro-étale slice is an equivalence on sheaves of types. -/
noncomputable instance directImageIsEquivalence
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    ((bigAffineInclusion X S).sheafPushforwardCocontinuous (Type (max u v))
      (bigAffineTopology X S) (bigTopology X S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence
    (bigAffineInclusion X S)

end AlgebraicGeometry.ChosenBigProetaleSite.AffineComparison
