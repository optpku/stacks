module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Affine
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous

/-!
# Comparison for affine standard sites

This module records special cocontinuity of the affine inclusion and the
resulting equivalence on sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology.Affine

/-- The inclusion of the affine standard site in the big `τ`-site is special
cocontinuous. -/
instance inclusionIsSpecialCocontinuous (τ : StandardTopology) (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsSpecialCocontinuous
      (topology τ S) (τ.overTopology S) := sorry

/-- Direct image along the affine inclusion is an equivalence on sheaves of types. -/
noncomputable instance directImageIsEquivalence
    (τ : StandardTopology) (S : Scheme.{u}) :
    ((Scheme.AffineOver.forget S).sheafPushforwardCocontinuous (Type (u + 1))
      (topology τ S) (τ.overTopology S)).IsEquivalence := sorry

end AlgebraicGeometry.StandardTopology.Affine
