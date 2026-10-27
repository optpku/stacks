/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Grothendieck.LowerShriek
public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationTopos

/-!
# Inverse image of abelian sheaves along a fiberwise augmentation

The stage inverse images `a_n⁻¹` of an augmentation towards a site `D` on sheaves
of abelian groups, the identifications `f_φ⁻¹ a_m⁻¹ ≅ a_n⁻¹`, and the assembled
total inverse image `a⁻¹` on the Grothendieck construction.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
include h_fiberwise
include h_aug

/-- Stage inverse image `a_n⁻¹` of abelian sheaves, i.e. cocontinuous sheaf pullback along the
common composite `u_n`. -/
def IsAugmentation.abelianStageInverseImage (n : SimplexCategory) :
    Sheaf K.toGrothendieck AddCommGrpCat.{w} ⥤
      Sheaf (J (op n)).toGrothendieck AddCommGrpCat.{w} :=
  (IsAugmentation.stageFunctor F u0 n).sheafPullbackCocontinuous AddCommGrpCat.{w}
    (J (op n)).toGrothendieck K.toGrothendieck

/-- Unsheafified comparison of `a_n⁻¹ G` with the precomposition of `a_m⁻¹ G` along `u_φ`, using
the existing identification `u_φ ⋙ u_m ≅ u_n`. -/
private def IsAugmentation.abelianStageInverseImage_comp_whisker {m n : SimplexCategory}
    (φ : m ⟶ n) (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((IsAugmentation.stageFunctor F u0 n).op ⋙ G.obj) ≅
    (presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((F.map φ.op).toFunctor.op ⋙
        (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj) :=
  (presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).mapIso
    (isoWhiskerRight (NatIso.op (IsAugmentation.stageFunctor_compIso F J K u0 φ)) G.obj)

/-- Sheafification of the unit identifying precomposition of `a_m⁻¹ G` with `f_φ⁻¹ a_m⁻¹ G`. -/
private def IsAugmentation.abelianStageInverseImage_comp_unit {m n : SimplexCategory}
    (φ : m ⟶ n) (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((F.map φ.op).toFunctor.op ⋙
        (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj) ⟶
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck).obj
      ((IsAugmentation.abelianStageInverseImage F J K u0 m).obj G) :=
  (presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).map
    (whiskerLeft (F.map φ.op).toFunctor.op
      ((sheafificationAdjunction ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).unit.app
        ((IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj)))

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n)
    (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Cocontinuous pushforward of `sheafify(u_φ.op ⋙ u_m.op ⋙ G)` along `u_φ`. -/
private def IsAugmentation.abelianStageInverseImage_comp_precomposedPushforward
    {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    Sheaf (J (op m)).toGrothendieck AddCommGrpCat.{w} :=
  ((F.map φ.op).toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{w}
      (J (op n)).toGrothendieck (J (op m)).toGrothendieck).obj
    ((presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((F.map φ.op).toFunctor.op ⋙
        (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj))

/-- RAN unit of `u_m.op ⋙ G` followed by RAN of the sheafification unit of the precomposed
presenting presheaf `u_φ.op ⋙ u_m.op ⋙ G`. -/
private def IsAugmentation.abelianStageInverseImage_comp_unitInv_unit
    {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj ⟶
      (IsAugmentation.abelianStageInverseImage_comp_precomposedPushforward
        F J K u0 φ G).obj :=
  ((F.map φ.op).toFunctor.op.ranAdjunction AddCommGrpCat.{w}).unit.app
      ((IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj) ≫
    (F.map φ.op).toFunctor.op.ran.map
      ((sheafificationAdjunction ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).unit.app
        ((F.map φ.op).toFunctor.op ⋙
          (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj))

/-- Sheafification adjunct of `abelianStageInverseImage_comp_unitInv_unit`. -/
private def IsAugmentation.abelianStageInverseImage_comp_unitInv_adjunct
    {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (IsAugmentation.abelianStageInverseImage F J K u0 m).obj G ⟶
      IsAugmentation.abelianStageInverseImage_comp_precomposedPushforward F J K u0 φ G :=
  ((sheafificationAdjunction ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).homEquiv
      ((IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj)
      (IsAugmentation.abelianStageInverseImage_comp_precomposedPushforward
        F J K u0 φ G)).symm
    (IsAugmentation.abelianStageInverseImage_comp_unitInv_unit F J K u0 φ G)

/-- Presheaf map `u_φ.op ⋙ a_m⁻¹ G ⟶ sheafify(u_φ.op ⋙ u_m.op ⋙ G)` given by whiskering the
adjunct and applying the RAN counit of the precomposed sheafification. -/
private def IsAugmentation.abelianStageInverseImage_comp_unitInv_presheaf
    {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (F.map φ.op).toFunctor.op ⋙
        ((IsAugmentation.abelianStageInverseImage F J K u0 m).obj G).obj ⟶
      ((presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
        ((F.map φ.op).toFunctor.op ⋙
          (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj)).obj :=
  whiskerLeft (F.map φ.op).toFunctor.op
      (IsAugmentation.abelianStageInverseImage_comp_unitInv_adjunct F J K u0 φ G).hom ≫
    ((F.map φ.op).toFunctor.op.ranAdjunction AddCommGrpCat.{w}).counit.app
      ((presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
        ((F.map φ.op).toFunctor.op ⋙
          (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj)).obj

/-- Inverse of `abelianStageInverseImage_comp_unit`, as the sheafification adjunct of whiskering
the adjunct of `a_m⁻¹ G` and the RAN counit of the precomposed sheafification. -/
private def IsAugmentation.abelianStageInverseImage_comp_unitInv
    {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck).obj
      ((IsAugmentation.abelianStageInverseImage F J K u0 m).obj G) ⟶
    (presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((F.map φ.op).toFunctor.op ⋙
        (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj) :=
  ((sheafificationAdjunction ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).homEquiv
      ((F.map φ.op).toFunctor.op ⋙
        ((IsAugmentation.abelianStageInverseImage F J K u0 m).obj G).obj)
      ((presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
        ((F.map φ.op).toFunctor.op ⋙
          (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj))).symm
    (IsAugmentation.abelianStageInverseImage_comp_unitInv_presheaf F J K u0 φ G)

/-- The forward stage comparison followed by its inverse is the identity. -/
private theorem IsAugmentation.abelianStageInverseImage_comp_hom_inv_id
    {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (IsAugmentation.abelianStageInverseImage_comp_unitInv F J K u0 φ G ≫
      (IsAugmentation.abelianStageInverseImage_comp_whisker F J K u0 φ G).inv) ≫
      ((IsAugmentation.abelianStageInverseImage_comp_whisker F J K u0 φ G).hom ≫
      IsAugmentation.abelianStageInverseImage_comp_unit F J K u0 φ G) = 𝟙 _ := sorry

/-- The inverse stage comparison followed by the forward comparison is the identity. -/
private theorem IsAugmentation.abelianStageInverseImage_comp_inv_hom_id
    {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    ((IsAugmentation.abelianStageInverseImage_comp_whisker F J K u0 φ G).hom ≫
      IsAugmentation.abelianStageInverseImage_comp_unit F J K u0 φ G) ≫
      (IsAugmentation.abelianStageInverseImage_comp_unitInv F J K u0 φ G ≫
      (IsAugmentation.abelianStageInverseImage_comp_whisker F J K u0 φ G).inv) = 𝟙 _ := sorry

/-- Stage inverse-image comparisons commute with morphisms of abelian sheaves. -/
private theorem IsAugmentation.abelianStageInverseImage_comp_naturality
    {m n : SimplexCategory} (φ : m ⟶ n)
    {G H : Sheaf K.toGrothendieck AddCommGrpCat.{w}} (α : G ⟶ H) :
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
      (J (op n)).toGrothendieck (J (op m)).toGrothendieck).map
        ((IsAugmentation.abelianStageInverseImage F J K u0 m).map α) ≫
      (IsAugmentation.abelianStageInverseImage_comp_unitInv F J K u0 φ H ≫
      (IsAugmentation.abelianStageInverseImage_comp_whisker F J K u0 φ H).inv) =
    (IsAugmentation.abelianStageInverseImage_comp_unitInv F J K u0 φ G ≫
      (IsAugmentation.abelianStageInverseImage_comp_whisker F J K u0 φ G).inv) ≫
      (IsAugmentation.abelianStageInverseImage F J K u0 n).map α := sorry

/-- The inverse image along a simplex operator composed with the stage inverse image is naturally
isomorphic to the inverse image at the target stage. -/
def IsAugmentation.abelianStageInverseImage_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    IsAugmentation.abelianStageInverseImage F J K u0 m ⋙
      (F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck ≅
      IsAugmentation.abelianStageInverseImage F J K u0 n :=
  NatIso.ofComponents
    (fun G ↦
      { hom :=
          IsAugmentation.abelianStageInverseImage_comp_unitInv F J K u0 φ G ≫
            (IsAugmentation.abelianStageInverseImage_comp_whisker F J K u0 φ G).inv
        inv :=
          (IsAugmentation.abelianStageInverseImage_comp_whisker F J K u0 φ G).hom ≫
            IsAugmentation.abelianStageInverseImage_comp_unit F J K u0 φ G
        hom_inv_id := IsAugmentation.abelianStageInverseImage_comp_hom_inv_id F J K u0 φ G
        inv_hom_id := IsAugmentation.abelianStageInverseImage_comp_inv_hom_id F J K u0 φ G })
    (fun α ↦ IsAugmentation.abelianStageInverseImage_comp_naturality F J K u0 φ α)

/-- Restriction of the assembled abelian inverse image along a morphism of the Grothendieck
construction. -/
def IsAugmentation.abelianInverseImagePresheafMap
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) {X Y : Grothendieck F} (h : X ⟶ Y) :
    ((IsAugmentation.abelianStageInverseImage F J K u0 Y.base.unop).obj G).obj.obj
      (op Y.fiber) ⟶
    ((IsAugmentation.abelianStageInverseImage F J K u0 X.base.unop).obj G).obj.obj
      (op X.fiber) :=
  ((IsAugmentation.abelianStageInverseImage F J K u0 Y.base.unop).obj G).obj.map h.fiber.op ≫
    ((sheafificationAdjunction (J X.base).toGrothendieck AddCommGrpCat.{w}).unit.app
        ((F.map h.base).toFunctor.op ⋙
          ((IsAugmentation.abelianStageInverseImage F J K u0 Y.base.unop).obj G).obj)).app
      (op X.fiber) ≫
    ((IsAugmentation.abelianStageInverseImage_comp F J K u0 h.base.unop).hom.app G).hom.app
      (op X.fiber)

/-- The total fiberwise restriction maps preserve identities and composition. -/
private theorem IsAugmentation.abelianInverseImagePresheaf_laws
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (∀ U : Grothendieck F,
      IsAugmentation.abelianInverseImagePresheafMap F J K u0 G (𝟙 U) =
        𝟙 (((IsAugmentation.abelianStageInverseImage F J K u0 U.base.unop).obj G).obj.obj
          (op U.fiber))) ∧
    (∀ {U V W : Grothendieck F} (f : U ⟶ V) (g : V ⟶ W),
      IsAugmentation.abelianInverseImagePresheafMap F J K u0 G (f ≫ g) =
        IsAugmentation.abelianInverseImagePresheafMap F J K u0 G g ≫
          IsAugmentation.abelianInverseImagePresheafMap F J K u0 G f) := sorry

/-- The abelian presheaf with value at `U` given by the stage inverse image at its fiber. -/
def IsAugmentation.abelianInverseImagePresheaf
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (Grothendieck F)ᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj W :=
    ((IsAugmentation.abelianStageInverseImage F J K u0 W.unop.base.unop).obj G).obj.obj
      (op W.unop.fiber)
  map {W Z} η := IsAugmentation.abelianInverseImagePresheafMap F J K u0 G η.unop
  map_id W := (IsAugmentation.abelianInverseImagePresheaf_laws F J K u0 G).1 W.unop
  map_comp f g := (IsAugmentation.abelianInverseImagePresheaf_laws F J K u0 G).2 g.unop f.unop

/-- The stagewise assembled abelian inverse-image presheaf is a sheaf. -/
private theorem IsAugmentation.abelianInverseImage_isSheaf
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    Presheaf.IsSheaf (topology F J)
      (IsAugmentation.abelianInverseImagePresheaf F J K u0 G) := sorry

/-- Stagewise inverse images of a sheaf morphism commute with total fiberwise restriction. -/
private theorem IsAugmentation.abelianInverseImage_map_naturality
    {G H : Sheaf K.toGrothendieck AddCommGrpCat.{w}} (α : G ⟶ H)
    {W Z : (Grothendieck F)ᵒᵖ} (η : W ⟶ Z) :
    (IsAugmentation.abelianInverseImagePresheaf F J K u0 G).map η ≫
        ((IsAugmentation.abelianStageInverseImage F J K u0 Z.unop.base.unop).map α).hom.app
          (op Z.unop.fiber) =
      ((IsAugmentation.abelianStageInverseImage F J K u0 W.unop.base.unop).map α).hom.app
          (op W.unop.fiber) ≫
        (IsAugmentation.abelianInverseImagePresheaf F J K u0 H).map η := sorry

/-- The sheaf morphism obtained by applying inverse image at each stage. -/
private def IsAugmentation.abelianInverseImageMap
    {G H : Sheaf K.toGrothendieck AddCommGrpCat.{w}} (α : G ⟶ H) :
    (⟨IsAugmentation.abelianInverseImagePresheaf F J K u0 G,
      IsAugmentation.abelianInverseImage_isSheaf F J K u0 G⟩ :
        Sheaf (topology F J) AddCommGrpCat.{w}) ⟶
      ⟨IsAugmentation.abelianInverseImagePresheaf F J K u0 H,
        IsAugmentation.abelianInverseImage_isSheaf F J K u0 H⟩ :=
  ObjectProperty.homMk
    { app := fun W ↦
        ((IsAugmentation.abelianStageInverseImage F J K u0 W.unop.base.unop).map α).hom.app
          (op W.unop.fiber)
      naturality := fun _ _ η ↦
        IsAugmentation.abelianInverseImage_map_naturality F J K u0 α η }

/-- Stagewise inverse image of sheaf morphisms preserves identities and composition. -/
private theorem IsAugmentation.abelianInverseImage_map_laws :
    (∀ G : Sheaf K.toGrothendieck AddCommGrpCat.{w},
      IsAugmentation.abelianInverseImageMap F J K u0 (𝟙 G) =
        𝟙 (⟨IsAugmentation.abelianInverseImagePresheaf F J K u0 G,
          IsAugmentation.abelianInverseImage_isSheaf F J K u0 G⟩ :
            Sheaf (topology F J) AddCommGrpCat.{w})) ∧
    (∀ {G H L : Sheaf K.toGrothendieck AddCommGrpCat.{w}} (α : G ⟶ H) (β : H ⟶ L),
      IsAugmentation.abelianInverseImageMap F J K u0 (α ≫ β) =
        IsAugmentation.abelianInverseImageMap F J K u0 α ≫
          IsAugmentation.abelianInverseImageMap F J K u0 β) := sorry

/-- Inverse image of abelian sheaves along the total augmentation. -/
def IsAugmentation.abelianInverseImage :
    Sheaf K.toGrothendieck AddCommGrpCat.{w} ⥤
      Sheaf (topology F J) AddCommGrpCat.{w} where
  obj G := ⟨IsAugmentation.abelianInverseImagePresheaf F J K u0 G,
    IsAugmentation.abelianInverseImage_isSheaf F J K u0 G⟩
  map α := IsAugmentation.abelianInverseImageMap F J K u0 α
  map_id := (IsAugmentation.abelianInverseImage_map_laws F J K u0).1
  map_comp := (IsAugmentation.abelianInverseImage_map_laws F J K u0).2

/-- Sections of `a⁻¹ G` over `X` are the sections of `a_{deg X}⁻¹ G` over the fiber of `X`. -/
theorem IsAugmentation.abelianInverseImage_obj_app
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (X : Grothendieck F) :
    ((IsAugmentation.abelianInverseImage F J K u0).obj G).obj.obj (op X) =
      ((IsAugmentation.abelianStageInverseImage F J K u0 X.base.unop).obj G).obj.obj
        (op X.fiber) := sorry

/-- Restriction of the total inverse image and the stage inverse image have identical restriction
maps. -/
private theorem IsAugmentation.restrictAbelianInverseImage_naturality
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (n : SimplexCategory)
    {U V : (F.obj (op n))ᵒᵖ} (f : U ⟶ V) :
    ((fiberRestrict F J AddCommGrpCat.{w} n).obj
      ((IsAugmentation.abelianInverseImage F J K u0).obj G)).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ ((IsAugmentation.abelianStageInverseImage F J K u0 n).obj G).obj.map f := sorry

/-- Identity-on-sections identification of the degree-`n` restriction of `a⁻¹ G` with `a_n⁻¹ G`. -/
def IsAugmentation.restrictAbelianInverseImageIso
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (n : SimplexCategory) :
    (fiberRestrict F J AddCommGrpCat.{w} n).obj
      ((IsAugmentation.abelianInverseImage F J K u0).obj G) ≅
    (IsAugmentation.abelianStageInverseImage F J K u0 n).obj G :=
  ObjectProperty.isoMk _
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (fun f ↦ IsAugmentation.restrictAbelianInverseImage_naturality F J K u0 G n f))

/-- The forward map of `restrictAbelianInverseImageIso` is identity on sections. -/
theorem IsAugmentation.restrictAbelianInverseImageIso_hom_app
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (n : SimplexCategory)
    (U : (F.obj (op n))ᵒᵖ) :
    ((IsAugmentation.restrictAbelianInverseImageIso F J K u0 G n).hom.hom.app U) =
      𝟙 _ := sorry

/-- The inverse map of `restrictAbelianInverseImageIso` is identity on sections. -/
theorem IsAugmentation.restrictAbelianInverseImageIso_inv_app
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (n : SimplexCategory)
    (U : (F.obj (op n))ᵒᵖ) :
    ((IsAugmentation.restrictAbelianInverseImageIso F J K u0 G n).inv.hom.app U) =
      𝟙 _ := sorry

end CategoryTheory.Grothendieck

