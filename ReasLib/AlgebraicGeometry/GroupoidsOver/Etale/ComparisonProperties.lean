/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPseudofunctor
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SheafComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.InverseImage

/-!
# Functoriality of the small-étale inverse-image comparison

The small-étale comparison morphism `c_φ` is functorial in `φ`, an isomorphism
when `φ` lies over an étale scheme morphism, and compatible with inverse image
along a 1-morphism of categories fibred in groupoids.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Scheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

section ComparisonComp

variable {x y z : X.total} (φ : x ⟶ y) (ψ : y ⟶ z)
variable (F : Sheaf X.etaleTopology (Type (u + 1)))
variable [HasWeakSheafify (X.p.obj x).left.smallEtaleTopology (Type (u + 1))]
variable [HasWeakSheafify (X.p.obj y).left.smallEtaleTopology (Type (u + 1))]
variable [∀ P : (X.p.obj y).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (X.p.map φ).left).op.HasLeftKanExtension P]
variable [∀ P : (X.p.obj z).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (X.p.map ψ).left).op.HasLeftKanExtension P]
variable [∀ P : (X.p.obj z).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (X.p.map (φ ≫ ψ)).left).op.HasLeftKanExtension P]
variable [∀ P : (X.p.obj z).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback ((X.p.map φ).left ≫ (X.p.map ψ).left)).op.HasLeftKanExtension P]

/-- Functoriality of inverse-image comparison: `c_{ψ ∘ φ}` equals the composite
`a_small⁻¹(c_ψ)` then `c_φ` after identifying `(b ∘ a)_small⁻¹` with
`a_small⁻¹ ∘ b_small⁻¹`. -/
theorem comparison_comp :
    comparison (φ ≫ ψ) F =
      (eqToHom (congrArg
        (fun a : (X.p.obj x).left ⟶ (X.p.obj z).left ↦
          (EtaleSheaf.pullback a).obj (restrictSmallEtaleSheaf F z))
        (congrArg (fun a : X.p.obj x ⟶ X.p.obj z ↦ a.left) (X.p.map_comp φ ψ))) :
        (EtaleSheaf.pullback (X.p.map (φ ≫ ψ)).left).obj (restrictSmallEtaleSheaf F z) ⟶
          (EtaleSheaf.pullback ((X.p.map φ).left ≫ (X.p.map ψ).left)).obj
            (restrictSmallEtaleSheaf F z)) ≫
        (EtaleSheaf.pullbackComp (X.p.map ψ).left (X.p.map φ).left).inv.app
          (restrictSmallEtaleSheaf F z) ≫
        (EtaleSheaf.pullback (X.p.map φ).left).map (comparison ψ F) ≫
          comparison φ F :=
  sorry

/-- If `φ` lies over an étale morphism of schemes, then `comparison φ F` is an
isomorphism. -/
instance comparison_isIso [Etale (X.p.map φ).left] : IsIso (comparison φ F) :=
  sorry

end ComparisonComp

section ComparisonInverseImage

variable {Y : GroupoidsOver S} (f : Y ⟶ X)
variable {y' y : Y.total} (ψY : y' ⟶ y)
variable (F : Sheaf X.etaleTopology (Type (u + 1)))
variable [HasSheafify Y.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify Y.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify X.etaleTopology (Type (u + 1))]
variable [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (Y.p.obj y').left.smallEtaleTopology (Type (u + 1))]
variable [∀ P : (Y.p.obj y).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (Y.p.map ψY).left).op.HasLeftKanExtension P]
variable [HasWeakSheafify (X.p.obj ((toFunctor f).obj y')).left.smallEtaleTopology
    (Type (u + 1))]
variable [∀ P : (X.p.obj ((toFunctor f).obj y)).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (X.p.map ((toFunctor f).map ψY)).left).op.HasLeftKanExtension P]

/-- Source identification of reindexed `c_{f(ψ)}` on an étale neighborhood of
`p(y')`. -/
private theorem restrictSmallEtaleSheaf_inverseImage_comp_app_source_eq
    (V' : ((Y.p.obj y').left.Etale)ᵒᵖ) :
    ((EtaleSheaf.pullback (Y.p.map ψY).left).obj
        (restrictSmallEtaleSheaf_reindex f y F)).obj.obj V' =
      ((EtaleSheaf.pullback (X.p.map ((toFunctor f).map ψY)).left).obj
        (restrictSmallEtaleSheaf F ((toFunctor f).obj y))).obj.obj
          (op (transportEtale f y' (unop V'))) :=
  sorry

/-- Component of the reindexed comparison `c_{f(ψ)}` on an étale neighborhood of
`p(y')`. -/
def restrictSmallEtaleSheaf_inverseImage_comp_app
    (V' : ((Y.p.obj y').left.Etale)ᵒᵖ) :
    ((EtaleSheaf.pullback (Y.p.map ψY).left).obj
        (restrictSmallEtaleSheaf_reindex f y F)).obj.obj V' ⟶
      (restrictSmallEtaleSheaf_reindex f y' F).obj.obj V' :=
  eqToHom (by exact restrictSmallEtaleSheaf_inverseImage_comp_app_source_eq f ψY F V') ≫
    (comparison ((toFunctor f).map ψY) F).hom.app
      (op (transportEtale f y' (unop V')))

/-- The reindexed comparison `c_{f(ψ)}` as a morphism of sheaves on the small
étale site of `p(y')`. -/
def restrictSmallEtaleSheaf_inverseImage_comp :
    (EtaleSheaf.pullback (Y.p.map ψY).left).obj
        (restrictSmallEtaleSheaf_reindex f y F) ⟶
      restrictSmallEtaleSheaf_reindex f y' F :=
  ⟨{ app := fun V' ↦ restrictSmallEtaleSheaf_inverseImage_comp_app f ψY F V'
     naturality := sorry }⟩

/-- Sections of `restrictSmallEtaleSheaf_inverseImage_comp` are the components
`restrictSmallEtaleSheaf_inverseImage_comp_app`. -/
theorem restrictSmallEtaleSheaf_inverseImage_comp_hom_app
    (V' : ((Y.p.obj y').left.Etale)ᵒᵖ) :
    (restrictSmallEtaleSheaf_inverseImage_comp f ψY F).hom.app V' =
      restrictSmallEtaleSheaf_inverseImage_comp_app f ψY F V' :=
  rfl

/-- After the identifications of `restrictSmallEtaleSheaf_inverseImage`, the
comparison map `c_ψ` of `f⁻¹ F` equals the comparison map `c_{f(ψ)}` of `F`. -/
theorem comparison_inverseImage :
    comparison ψY
          (((toCartesianBasedFunctor f).morphismOfTopoiIn
              (StandardTopology.etale.overTopology S)).inverseImage.obj F) ≫
        (restrictSmallEtaleSheaf_inverseImage f y' F).hom =
      (EtaleSheaf.pullback (Y.p.map ψY).left).map
          (restrictSmallEtaleSheaf_inverseImage f y F).hom ≫
        restrictSmallEtaleSheaf_inverseImage_comp f ψY F :=
  sorry

end ComparisonInverseImage

end AlgebraicGeometry.GroupoidsOver
