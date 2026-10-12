/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPseudofunctor
public import stacks_project.Chap96.«96_9_2_2_Comparison»
public import stacks_project.Chap96.Lemma_96_9_3_Restriction

/-!
# Functoriality of the small-étale inverse-image comparison

The comparison morphism `c_φ` of 96.9.2.2 is functorial in `φ`, an isomorphism
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

/-- The scheme morphism underlying a composite in a groupoid fibration is the
composite of the underlying scheme morphisms. -/
theorem map_left_comp {x y z : X.total} (φ : x ⟶ y) (ψ : y ⟶ z) :
    (X.p.map (φ ≫ ψ)).left = (X.p.map φ).left ≫ (X.p.map ψ).left :=
  sorry

/-- Objectwise equality of small-étale pullbacks along `map_left_comp`. -/
theorem pullback_map_comp_obj_eq {x y z : X.total} (φ : x ⟶ y) (ψ : y ⟶ z)
    (G : Sheaf (X.p.obj z).left.smallEtaleTopology (Type (u + 1))) :
    (EtaleSheaf.pullback (X.p.map (φ ≫ ψ)).left).obj G =
      (EtaleSheaf.pullback ((X.p.map φ).left ≫ (X.p.map ψ).left)).obj G :=
  sorry

/-- Transport of small-étale sheaf pullback along functoriality of `X.p`. -/
def pullback_map_comp_iso {x y z : X.total} (φ : x ⟶ y) (ψ : y ⟶ z) :
    EtaleSheaf.pullback (X.p.map (φ ≫ ψ)).left ≅
      EtaleSheaf.pullback ((X.p.map φ).left ≫ (X.p.map ψ).left) :=
  NatIso.ofComponents
    (fun G ↦
      { hom := eqToHom (pullback_map_comp_obj_eq φ ψ G)
        inv := eqToHom (pullback_map_comp_obj_eq φ ψ G).symm
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ ↦ sorry)

/-- `pullback_map_comp_iso` is objectwise `eqToHom` of `pullback_map_comp_obj_eq`. -/
theorem pullback_map_comp_iso_eq {x y z : X.total} (φ : x ⟶ y) (ψ : y ⟶ z)
    (G : Sheaf (X.p.obj z).left.smallEtaleTopology (Type (u + 1))) :
    (pullback_map_comp_iso φ ψ).hom.app G = eqToHom (pullback_map_comp_obj_eq φ ψ G) :=
  sorry

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
      (pullback_map_comp_iso φ ψ).hom.app (restrictSmallEtaleSheaf F z) ≫
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

/-- The scheme morphism underlying `ψ` on `Y` agrees with the scheme morphism
underlying `f(ψ)` on `X`, after identifying `p(f(y))` with `p(y)`. -/
theorem map_left_toFunctor :
    (Y.p.map ψY).left =
      eqToHom (map_obj_left_eq f y').symm ≫
        (X.p.map ((toFunctor f).map ψY)).left ≫
          eqToHom (map_obj_left_eq f y) :=
  sorry

/-- Source/target identification for the reindexed comparison `c_{f(ψ)}`. -/
theorem restrictSmallEtaleSheaf_inverseImage_comp_eq :
    (EtaleSheaf.pullback (Y.p.map ψY).left).obj
        (restrictSmallEtaleSheaf_reindex f y F) =
      (map_obj_left_eq f y').symm ▸
        (EtaleSheaf.pullback (X.p.map ((toFunctor f).map ψY)).left).obj
          (restrictSmallEtaleSheaf F ((toFunctor f).obj y)) :=
  sorry

/-- Source identification of reindexed `c_{f(ψ)}` on an étale neighborhood of
`p(y')`. -/
theorem restrictSmallEtaleSheaf_inverseImage_comp_app_source_eq
    (V' : ((Y.p.obj y').left.Etale)ᵒᵖ) :
    ((EtaleSheaf.pullback (Y.p.map ψY).left).obj
        (restrictSmallEtaleSheaf_reindex f y F)).obj.obj V' =
      ((EtaleSheaf.pullback (X.p.map ((toFunctor f).map ψY)).left).obj
        (restrictSmallEtaleSheaf F ((toFunctor f).obj y))).obj.obj
          (op (transportEtale f y' (unop V'))) :=
  sorry

/-- Target identification of reindexed `c_{f(ψ)}` on an étale neighborhood of
`p(y')`. -/
theorem restrictSmallEtaleSheaf_inverseImage_comp_app_target_eq
    (V' : ((Y.p.obj y').left.Etale)ᵒᵖ) :
    (restrictSmallEtaleSheaf F ((toFunctor f).obj y')).obj.obj
        (op (transportEtale f y' (unop V'))) =
      (restrictSmallEtaleSheaf_reindex f y' F).obj.obj V' :=
  sorry

/-- Component of the reindexed comparison `c_{f(ψ)}` on an étale neighborhood of
`p(y')`. -/
def restrictSmallEtaleSheaf_inverseImage_comp_app
    (V' : ((Y.p.obj y').left.Etale)ᵒᵖ) :
    ((EtaleSheaf.pullback (Y.p.map ψY).left).obj
        (restrictSmallEtaleSheaf_reindex f y F)).obj.obj V' ⟶
      (restrictSmallEtaleSheaf_reindex f y' F).obj.obj V' :=
  eqToHom (restrictSmallEtaleSheaf_inverseImage_comp_app_source_eq f ψY F V') ≫
    (comparison ((toFunctor f).map ψY) F).hom.app
      (op (transportEtale f y' (unop V'))) ≫
    eqToHom (restrictSmallEtaleSheaf_inverseImage_comp_app_target_eq f F V')

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
  sorry

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
