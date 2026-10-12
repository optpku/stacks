/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Lemma_85_3_5_Fiber
public import stacks_project.Chap85.Lemma_85_4_2_Fiberwise

/-!
# Inverse image of abelian sheaves along a fiberwise augmentation

The stage inverse images `a_n⁻¹` of an augmentation towards a site `D` on sheaves
of abelian groups, the identifications `f_φ⁻¹ a_m⁻¹ ≅ a_n⁻¹`, and the assembled
total inverse image `a⁻¹` on the Grothendieck construction.
-/

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

/-- Stage inverse image `a_n⁻¹` of abelian sheaves, i.e. cocontinuous sheaf pullback
along the common composite `u_n`. -/
def IsAugmentation.abelianStageInverseImage (n : SimplexCategory) :
    Sheaf K.toGrothendieck AddCommGrpCat.{w} ⥤
      Sheaf (J (op n)).toGrothendieck AddCommGrpCat.{w} :=
  (IsAugmentation.stageFunctor F u0 n).sheafPullbackCocontinuous AddCommGrpCat.{w}
    (J (op n)).toGrothendieck K.toGrothendieck

/-- `abelianStageInverseImage n` is cocontinuous sheaf pullback along `u_n`. -/
theorem IsAugmentation.abelianStageInverseImage_eq (n : SimplexCategory) :
    IsAugmentation.abelianStageInverseImage F J K u0 n =
      (IsAugmentation.stageFunctor F u0 n).sheafPullbackCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck K.toGrothendieck :=
  sorry

/-- Unsheafified comparison of `a_n⁻¹ G` with the precomposition of `a_m⁻¹ G` along
`u_φ`, using the existing identification `u_φ ⋙ u_m ≅ u_n`. -/
def IsAugmentation.abelianStageInverseImage_comp_whisker {m n : SimplexCategory}
    (φ : m ⟶ n) (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((IsAugmentation.stageFunctor F u0 n).op ⋙ G.obj) ≅
    (presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((F.map φ.op).toFunctor.op ⋙
        (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj) :=
  (presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).mapIso
    (isoWhiskerRight (NatIso.op (IsAugmentation.stageFunctor_compIso F J K u0 φ)) G.obj)

/-- Sheafification of the unit identifying precomposition of `a_m⁻¹ G` with
`f_φ⁻¹ a_m⁻¹ G`. -/
def IsAugmentation.abelianStageInverseImage_comp_unit {m n : SimplexCategory}
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
def IsAugmentation.abelianStageInverseImage_comp_precomposedPushforward
    {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    Sheaf (J (op m)).toGrothendieck AddCommGrpCat.{w} :=
  ((F.map φ.op).toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{w}
      (J (op n)).toGrothendieck (J (op m)).toGrothendieck).obj
    ((presheafToSheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((F.map φ.op).toFunctor.op ⋙
        (IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj))

/-- RAN unit of `u_m.op ⋙ G` followed by RAN of the sheafification unit of the
precomposed presenting presheaf `u_φ.op ⋙ u_m.op ⋙ G`. -/
def IsAugmentation.abelianStageInverseImage_comp_unitInv_unit
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
def IsAugmentation.abelianStageInverseImage_comp_unitInv_adjunct
    {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (IsAugmentation.abelianStageInverseImage F J K u0 m).obj G ⟶
      IsAugmentation.abelianStageInverseImage_comp_precomposedPushforward F J K u0 φ G :=
  ((sheafificationAdjunction ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).homEquiv
      ((IsAugmentation.stageFunctor F u0 m).op ⋙ G.obj)
      (IsAugmentation.abelianStageInverseImage_comp_precomposedPushforward
        F J K u0 φ G)).symm
    (IsAugmentation.abelianStageInverseImage_comp_unitInv_unit F J K u0 φ G)

/-- Presheaf map `u_φ.op ⋙ a_m⁻¹ G ⟶ sheafify(u_φ.op ⋙ u_m.op ⋙ G)` given by
whiskering the adjunct and applying the RAN counit of the precomposed
sheafification. -/
def IsAugmentation.abelianStageInverseImage_comp_unitInv_presheaf
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

/-- Inverse of `abelianStageInverseImage_comp_unit`, as the sheafification adjunct of
whiskering the adjunct of `a_m⁻¹ G` and the RAN counit of the precomposed
sheafification. -/
def IsAugmentation.abelianStageInverseImage_comp_unitInv
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

/-- Inverse-image form of `a_m ∘ f_φ = a_n` on abelian sheaves. Both directions are
explicit composites; only the inverse laws and naturality are deferred. -/
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
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Restriction of the assembled abelian inverse image along a morphism of the
Grothendieck construction. -/
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

/-- The assembled abelian presheaf on `Grothendieck F` whose value at `X` is
`a_{deg X}⁻¹ G` at the fiber of `X`. -/
def IsAugmentation.abelianInverseImagePresheaf
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (Grothendieck F)ᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj W :=
    ((IsAugmentation.abelianStageInverseImage F J K u0 W.unop.base.unop).obj G).obj.obj
      (op W.unop.fiber)
  map {W Z} η := IsAugmentation.abelianInverseImagePresheafMap F J K u0 G η.unop
  map_id := sorry
  map_comp := sorry

/-- Inverse image `a⁻¹` of abelian sheaves along the total fiberwise augmentation. -/
def IsAugmentation.abelianInverseImage :
    Sheaf K.toGrothendieck AddCommGrpCat.{w} ⥤
      Sheaf (topology F J) AddCommGrpCat.{w} where
  obj G := ⟨IsAugmentation.abelianInverseImagePresheaf F J K u0 G, sorry⟩
  map {G H} α := ObjectProperty.homMk
    { app := fun W ↦
        ((IsAugmentation.abelianStageInverseImage F J K u0 W.unop.base.unop).map α).hom.app
          (op W.unop.fiber)
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Sections of `a⁻¹ G` over `X` are the sections of `a_{deg X}⁻¹ G` over the fiber of `X`. -/
theorem IsAugmentation.abelianInverseImage_obj_app
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (X : Grothendieck F) :
    ((IsAugmentation.abelianInverseImage F J K u0).obj G).obj.obj (op X) =
      ((IsAugmentation.abelianStageInverseImage F J K u0 X.base.unop).obj G).obj.obj
        (op X.fiber) :=
  sorry

variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]

/-- Identity-on-sections identification of the degree-`n` restriction of `a⁻¹ G`
with `a_n⁻¹ G`. -/
def IsAugmentation.restrictAbelianInverseImageIso
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (n : SimplexCategory) :
    (fiberRestrict F J AddCommGrpCat.{w} n).obj
      ((IsAugmentation.abelianInverseImage F J K u0).obj G) ≅
    (IsAugmentation.abelianStageInverseImage F J K u0 n).obj G where
  hom := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
  inv := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `restrictAbelianInverseImageIso` is identity on sections. -/
theorem IsAugmentation.restrictAbelianInverseImageIso_hom_app
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (n : SimplexCategory)
    (U : (F.obj (op n))ᵒᵖ) :
    ((IsAugmentation.restrictAbelianInverseImageIso F J K u0 G n).hom.hom.app U) =
      𝟙 _ :=
  sorry

/-- The inverse map of `restrictAbelianInverseImageIso` is identity on sections. -/
theorem IsAugmentation.restrictAbelianInverseImageIso_inv_app
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (n : SimplexCategory)
    (U : (F.obj (op n))ᵒᵖ) :
    ((IsAugmentation.restrictAbelianInverseImageIso F J K u0 G n).inv.hom.app U) =
      𝟙 _ :=
  sorry

end CategoryTheory.Grothendieck

