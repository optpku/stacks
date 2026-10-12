/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Affine
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous

/-!
# Comparison of small affine and small pro-étale sites

The inclusion of affine objects of the small pro-étale site is special
cocontinuous. Restriction of type-valued sheaves along this inclusion is
therefore an equivalence.
-/

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ProEt.SmallAffineComparison

/-- The inclusion of affine objects of the small pro-étale site is special
cocontinuous. -/
theorem isSpecialCocontinuous (S : Scheme.{u}) :
    (affineInclusion S).IsSpecialCocontinuous (affineTopology S) (topology S) :=
  sorry

/-- The affine inclusion of the small pro-étale site carries its canonical
special-cocontinuity instance. -/
instance inclusionIsSpecialCocontinuous (S : Scheme.{u}) :
    (affineInclusion S).IsSpecialCocontinuous (affineTopology S) (topology S) :=
  isSpecialCocontinuous S

end AlgebraicGeometry.Scheme.ProEt.SmallAffineComparison

namespace AlgebraicGeometry.Scheme.ProEt

/-- Restriction of sheaves from the small pro-étale site to its affine full
subcategory. -/
noncomputable def affineRestriction (S : Scheme.{u}) :
    Sheaf (topology S) (Type (u + 1)) ⥤ Sheaf (affineTopology S) (Type (u + 1)) :=
  (affineInclusion S).sheafPushforwardContinuous (Type (u + 1)) (affineTopology S)
    (topology S)

/-- Restriction of a sheaf to an affine object is evaluation on the underlying
object of the small pro-étale site. -/
theorem affineRestriction_obj_val (S : Scheme.{u})
    (F : Sheaf (topology S) (Type (u + 1))) (U : Affine S) :
    ((affineRestriction S).obj F).obj.obj (op U) = F.obj.obj (op U.obj) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.Scheme.ProEt.SmallAffineComparison

/-- Restriction of type-valued sheaves along the affine inclusion is an
equivalence. -/
noncomputable instance restrictionIsEquivalence (S : Scheme.{u}) :
    (affineRestriction S).IsEquivalence := sorry

/-- The cocontinuous direct image from sheaves on affine objects to sheaves on
the small pro-étale site is an equivalence on sheaves of types. -/
noncomputable instance directImageIsEquivalence (S : Scheme.{u}) :
    ((affineInclusion S).sheafPushforwardCocontinuous (Type (u + 1))
      (affineTopology S) (topology S)).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.ProEt.SmallAffineComparison
