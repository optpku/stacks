/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtale
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

/-- The affine ind-étale inclusion presents a dense subsite of the small
pro-étale site of an affine scheme. -/
instance inclusionIsDenseSubsite (S : Scheme.{u}) [IsAffine S] :
    (affineIndEtaleInclusion S).IsDenseSubsite (affineIndEtaleTopology S)
      (topology S) := sorry

private instance inclusionHasPointwiseRightKanExtension (S : Scheme.{u}) [IsAffine S]
    (A : Type (u + 2)) [Category.{u + 1} A]
    [CategoryTheory.Limits.HasLimitsOfSize.{u, u + 1} A] :
    ∀ F : (AffineIndEtale S)ᵒᵖ ⥤ A,
      (affineIndEtaleInclusion S).op.HasPointwiseRightKanExtension F :=
  fun F Y => (inferInstance : CategoryTheory.Limits.HasLimit
    (StructuredArrow.proj Y (affineIndEtaleInclusion S).op ⋙ F))

/-- Restriction and right Kan extension along the affine ind-étale inclusion
form an equivalence of sheaf categories. -/
noncomputable def sheafEquivalence (S : Scheme.{u}) [IsAffine S]
    (A : Type (u + 2)) [Category.{u + 1} A]
    [CategoryTheory.Limits.HasLimitsOfSize.{u, u + 1} A] :
    Sheaf (topology S) A ≌ Sheaf (affineIndEtaleTopology S) A :=
  ((affineIndEtaleInclusion S).sheafAdjunctionCocontinuous A
    (affineIndEtaleTopology S) (topology S)).toEquivalence

/-- The inclusion of affine ind-étale objects of the small pro-étale site is
special cocontinuous. -/
theorem isSpecialCocontinuous (S : Scheme.{u}) [IsAffine S] :
    (affineIndEtaleInclusion S).IsSpecialCocontinuous (affineIndEtaleTopology S)
      (topology S) :=
  Functor.IsDenseSubsite.isSpecialCocontinuous (affineIndEtaleInclusion S)

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
  rfl

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.Scheme.ProEt.AffineIndEtaleComparison

/-- Restriction of type-valued sheaves along the affine ind-étale inclusion is
an equivalence. -/
noncomputable instance restrictionIsEquivalence (S : Scheme.{u}) [IsAffine S] :
    (affineIndEtaleRestriction S).IsEquivalence :=
  (sheafEquivalence S (Type (u + 1))).isEquivalence_functor

/-- The cocontinuous direct image from sheaves on affine ind-étale objects to
sheaves on the small pro-étale site is an equivalence on sheaves of types. -/
noncomputable instance directImageIsEquivalence (S : Scheme.{u}) [IsAffine S] :
    ((affineIndEtaleInclusion S).sheafPushforwardCocontinuous (Type (u + 1))
      (affineIndEtaleTopology S) (topology S)).IsEquivalence :=
  (sheafEquivalence S (Type (u + 1))).isEquivalence_inverse

end AlgebraicGeometry.Scheme.ProEt.AffineIndEtaleComparison
