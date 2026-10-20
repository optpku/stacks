module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Zariski
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.H.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenCovering

/-!
# Extensions of h-sheaves from full subcategories of schemes

This module gives the h-sheaf analogue of the canonical Zariski extension
interface for set-valued presheaves on schemes over a fixed base.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.Scheme.Over.Extension

/-- A canonical Zariski extension of an h-sheaf on a sufficiently rich full
subcategory is an h-sheaf on all schemes over the base. -/
theorem isHSheaf_of_isZariskiExtension
    {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type (u + 1))
    (F' : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hC_open : ContainsAffineOpens C)
    (hC_fp : ContainsFinitelyPresentedAffines C)
    (hF_h : Presheaf.IsSheaf
      (C.ι.restrictedTopology ((Scheme.hPrecoverage.toGrothendieck).over S)) F)
    (hF_limits : PreservesDirectedAffineLimits C F)
    (eF' : C.ι.op ⋙ F' ≅ F)
    (hF'_zariski : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F')
    (hF'_limits : Scheme.Over.PreservesDirectedAffineLimits S F')
    (hF'_unique :
      ∀ (G : (Over S)ᵒᵖ ⥤ Type (u + 1)) (eG : C.ι.op ⋙ G ≅ F),
        Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G →
        Scheme.Over.PreservesDirectedAffineLimits S G →
        ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF') :
    Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) F' := sorry

/-- An h-sheaf on a sufficiently rich full subcategory of schemes over a base,
preserving directed affine limits, extends to an h-sheaf on all schemes over
the base with the same limit-preservation property. -/
theorem existsHSheafExtension
    {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type (u + 1))
    (hC_open : ContainsAffineOpens C)
    (hC_fp : ContainsFinitelyPresentedAffines C)
    (hF_h : Presheaf.IsSheaf
      (C.ι.restrictedTopology ((Scheme.hPrecoverage.toGrothendieck).over S)) F)
    (hF_limits : PreservesDirectedAffineLimits C F) :
    ∃ (F' : (Over S)ᵒᵖ ⥤ Type (u + 1)), ∃ (eF' : C.ι.op ⋙ F' ≅ F),
      Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) F' ∧
        Scheme.Over.PreservesDirectedAffineLimits S F' := sorry

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

end AlgebraicGeometry.Scheme.Over.Extension
