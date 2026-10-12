/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.H.Sheaf
public import stacks_project.Chap61.Lemma_61_10_3_VSheaf

/-!
# Unique h-sheaf extensions and the V-sheaf property

This module records uniqueness among h-sheaf extensions that preserve
directed affine limits, together with the resulting V-sheaf extension of
a sheaf defined on a sufficiently rich full subcategory of `Over S`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open Scheme.Over

universe u w

namespace AlgebraicGeometry.Scheme.Over.Extension

/-- An h-sheaf on a sufficiently rich full subcategory of schemes over a
base, preserving directed affine limits, extends uniquely to an h-sheaf on
all schemes over the base with the same limit-preservation property. -/
theorem existsUniqueHSheafExtension
    {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type (u + 1))
    (hC_open : ContainsAffineOpens C)
    (hC_fp : ContainsFinitelyPresentedAffines C)
    (hF_h : Presheaf.IsSheaf
      (C.ι.restrictedTopology ((Scheme.hPrecoverage.toGrothendieck).over S)) F)
    (hF_limits : PreservesDirectedAffineLimits C F) :
    ∃ (F' : (Over S)ᵒᵖ ⥤ Type (u + 1)), ∃ (eF' : C.ι.op ⋙ F' ≅ F),
      ∃ (_ : Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) F'),
      ∃ (_ : Scheme.Over.PreservesDirectedAffineLimits S F'),
        ∀ (G : (Over S)ᵒᵖ ⥤ Type (u + 1)) (eG : C.ι.op ⋙ G ≅ F),
          Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) G →
          Scheme.Over.PreservesDirectedAffineLimits S G →
          ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF' := sorry

/-- Two h-sheaf extensions of the same restricted functor that preserve
directed affine limits are uniquely isomorphic compatibly with restriction. -/
theorem isoUnique_of_isHSheafExtension
    {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type (u + 1))
    (F' : (Over S)ᵒᵖ ⥤ Type (u + 1)) (eF' : C.ι.op ⋙ F' ≅ F)
    (hC_open : ContainsAffineOpens C)
    (hC_fp : ContainsFinitelyPresentedAffines C)
    (hF'_h : Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) F')
    (hF'_limits : Scheme.Over.PreservesDirectedAffineLimits S F')
    (G : (Over S)ᵒᵖ ⥤ Type (u + 1)) (eG : C.ι.op ⋙ G ≅ F)
    (hG_h : Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) G)
    (hG_limits : Scheme.Over.PreservesDirectedAffineLimits S G) :
    ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF' := sorry

/-- An h-sheaf on a sufficiently rich full subcategory of schemes over a
base, preserving directed affine limits, extends to an h-sheaf on all
schemes over the base that preserves directed affine limits, and this
h-sheaf limit-preserving extension is a V-sheaf. -/
theorem existsHSheafExtension_satisfiesVSheafProperty
    {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type (u + 1))
    (hC_open : ContainsAffineOpens C)
    (hC_fp : ContainsFinitelyPresentedAffines C)
    (hF_h : Presheaf.IsSheaf
      (C.ι.restrictedTopology ((Scheme.hPrecoverage.toGrothendieck).over S)) F)
    (hF_limits : PreservesDirectedAffineLimits C F) :
    ∃ (F' : (Over S)ᵒᵖ ⥤ Type (u + 1)), ∃ (eF' : C.ι.op ⋙ F' ≅ F),
      ∃ (_ : Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) F'),
      ∃ (_ : Scheme.Over.PreservesDirectedAffineLimits S F'),
        satisfiesVSheafProperty.{u, u + 1, w} S F' := sorry

end AlgebraicGeometry.Scheme.Over.Extension
