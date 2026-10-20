module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.H.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Over

/-!
# V-sheaf extensions from full subcategories of schemes

An h-sheaf preserving directed affine limits on a sufficiently rich full
subcategory extends to an h-sheaf on all schemes over the base that
preserves directed affine limits and satisfies the V-sheaf property.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u w

namespace AlgebraicGeometry.Scheme.Over.Extension

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
