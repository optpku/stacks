/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_12_21_AffineIndEtale
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous

/-!
# Comparison of affine ind-étale and small pro-étale sites

The inclusion of affine ind-étale objects of the small pro-étale site of an
affine scheme is special cocontinuous. Restriction of type-valued sheaves
along this inclusion is therefore an equivalence.
-/

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ProEt.AffineIndEtaleComparison

/-- The inclusion of affine ind-étale objects of the small pro-étale site is
special cocontinuous. -/
theorem isSpecialCocontinuous (S : Scheme.{u}) [IsAffine S] :
    (affineIndEtaleInclusion S).IsSpecialCocontinuous (affineIndEtaleTopology S)
      (topology S) :=
  sorry

/-- The affine ind-étale inclusion of the small pro-étale site carries its
canonical special-cocontinuity instance. -/
instance inclusionIsSpecialCocontinuous (S : Scheme.{u}) [IsAffine S] :
    (affineIndEtaleInclusion S).IsSpecialCocontinuous (affineIndEtaleTopology S)
      (topology S) :=
  isSpecialCocontinuous S

end AlgebraicGeometry.Scheme.ProEt.AffineIndEtaleComparison

namespace AlgebraicGeometry.Scheme.ProEt

/-- Restriction of sheaves from the small pro-étale site to its affine
ind-étale full subcategory. -/
noncomputable def affineIndEtaleRestriction (S : Scheme.{u}) [IsAffine S] :
    Sheaf (topology S) (Type (u + 1)) ⥤
      Sheaf (affineIndEtaleTopology S) (Type (u + 1)) :=
  (affineIndEtaleInclusion S).sheafPushforwardContinuous (Type (u + 1))
    (affineIndEtaleTopology S) (topology S)

/-- Restriction of a sheaf to an affine ind-étale object is evaluation on the
underlying object of the small pro-étale site. -/
theorem affineIndEtaleRestriction_obj_val (S : Scheme.{u}) [IsAffine S]
    (F : Sheaf (topology S) (Type (u + 1))) (U : AffineIndEtale S) :
    ((affineIndEtaleRestriction S).obj F).obj.obj (op U) = F.obj.obj (op U.obj) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.Scheme.ProEt.AffineIndEtaleComparison

/-- Restriction of type-valued sheaves along the affine ind-étale inclusion is
an equivalence. -/
noncomputable instance restrictionIsEquivalence (S : Scheme.{u}) [IsAffine S] :
    (affineIndEtaleRestriction S).IsEquivalence := sorry

/-- The cocontinuous direct image from sheaves on affine ind-étale objects to
sheaves on the small pro-étale site is an equivalence on sheaves of types. -/
noncomputable instance directImageIsEquivalence (S : Scheme.{u}) [IsAffine S] :
    ((affineIndEtaleInclusion S).sheafPushforwardCocontinuous (Type (u + 1))
      (affineIndEtaleTopology S) (topology S)).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.ProEt.AffineIndEtaleComparison
