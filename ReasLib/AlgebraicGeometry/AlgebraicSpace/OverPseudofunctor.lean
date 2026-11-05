/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Algebraic-space slices as a pseudofunctor

Pullback along a morphism of algebraic spaces over a scheme `S` gives the
contravariant pseudofunctor whose fibre over `X` is the slice category `Over X`.
Transition functors are given by slice pullback along each morphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

/-- The cone identity witnessing that `𝟙 X.left` and `X.hom` form a cone over `X.hom` and
`𝟙 W`. -/
theorem overPullbackId_w {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    𝟙 X.left ≫ X.hom = X.hom ≫ 𝟙 W := by simp

/-- The underlying forward map of identity slice pullback, as the first projection. -/
def overPullbackIdHom {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    ((overPullback (𝟙 W)).obj X).left ⟶ X.left :=
  overPullbackFst (𝟙 W) X

/-- `overPullbackIdHom` is the first projection of slice pullback along an identity. -/
theorem overPullbackIdHom_eq {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    overPullbackIdHom X = overPullbackFst (𝟙 W) X := rfl

/-- The underlying inverse map of identity slice pullback, induced by the identity cone. -/
def overPullbackIdInv {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    X.left ⟶ ((overPullback (𝟙 W)).obj X).left :=
  ReasLibPullback.pullbackLift X.hom (𝟙 W) (𝟙 X.left) X.hom (overPullbackId_w X)

/-- `overPullbackIdInv` is the mediating map of the identity cone. -/
theorem overPullbackIdInv_eq {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    overPullbackIdInv X =
      ReasLibPullback.pullbackLift X.hom (𝟙 W) (𝟙 X.left) X.hom (overPullbackId_w X) := rfl

/-- Slice pullback along an identity morphism is naturally the identity functor. -/
noncomputable def overPullbackIdIso {S : Scheme.{u}} (W : AlgebraicSpace S) :
    overPullback (𝟙 W) ≅ 𝟭 (Over W) :=
  overPullbackIso (𝟙 W) ≪≫ Over.pullbackId

/-- The identity comparison is transported from the standard slice-pullback identity. -/
theorem overPullbackIdIso_standard {S : Scheme.{u}} (W : AlgebraicSpace S) :
    overPullbackIdIso W = overPullbackIso (𝟙 W) ≪≫ Over.pullbackId := rfl

private theorem standardPullbackId_hom {S : Scheme.{u}} (W : AlgebraicSpace S)
    (X : Over W) :
    ((Over.pullbackId (X := W)).hom.app X).left =
      Limits.pullback.fst X.hom (𝟙 W) := by
  have h := congrArg (fun k ↦ k.left)
    (conjugateEquiv_counit (Over.mapPullbackAdj (𝟙 W)) (Adjunction.id (C := Over W))
      (Over.mapId W).inv X)
  simpa [Over.pullbackId, conjugateIsoEquiv] using h

/-- The component of `overPullbackIdIso` is identity slice pullback on objects. -/
theorem overPullbackIdIso_hom_app {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    ((overPullbackIdIso W).hom.app X).left = overPullbackIdHom X := by
  change ((overPullbackIso (𝟙 W)).hom.app X).left ≫
    ((Over.pullbackId (X := W)).hom.app X).left = overPullbackFst (𝟙 W) X
  rw [standardPullbackId_hom, overPullbackIso_hom_fst]

/-- The first factor of the composite-pullback comparison, into the intermediate slice. -/
def overPullbackCompMid {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullback (g ≫ f)).obj X).left ⟶ ((overPullback f).obj X).left :=
  ReasLibPullback.pullbackLift X.hom f (overPullbackFst (g ≫ f) X)
    (overPullbackSnd (g ≫ f) X ≫ g)
    (by simpa only [Category.assoc] using overPullback_condition (g ≫ f) X)

/-- `overPullbackCompMid` recovers the first projection of the composite pullback. -/
theorem overPullbackCompMid_fst {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    overPullbackCompMid f g X ≫ overPullbackFst f X =
      overPullbackFst (g ≫ f) X :=
  ReasLibPullback.pullbackLift_fst _ _ _ _ _

/-- The intermediate comparison recovers the projection to the intermediate base. -/
@[reassoc (attr := simp)]
theorem overPullbackCompMid_snd {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    overPullbackCompMid f g X ≫ overPullbackSnd f X = overPullbackSnd (g ≫ f) X ≫ g :=
  ReasLibPullback.pullbackLift_snd _ _ _ _ _

/-- Underlying forward map of iterated slice pullback comparison. -/
def overPullbackCompHom {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullback (g ≫ f)).obj X).left ⟶
      ((overPullback g).obj ((overPullback f).obj X)).left :=
  ReasLibPullback.pullbackLift ((overPullback f).obj X).hom g (overPullbackCompMid f g X)
    (overPullbackSnd (g ≫ f) X)
    (ReasLibPullback.pullbackLift_snd _ _ _ _ _)

/-- The first projection of the iterated comparison is its intermediate comparison. -/
@[reassoc (attr := simp)]
theorem overPullbackCompHom_fst {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    overPullbackCompHom f g X ≫ overPullbackFst g ((overPullback f).obj X) =
      overPullbackCompMid f g X :=
  ReasLibPullback.pullbackLift_fst _ _ _ _ _

/-- `overPullbackCompHom` recovers the second projection of the composite pullback. -/
theorem overPullbackCompHom_snd {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    overPullbackCompHom f g X ≫ overPullbackSnd g ((overPullback f).obj X) =
      overPullbackSnd (g ≫ f) X :=
  ReasLibPullback.pullbackLift_snd _ _ _ _ _

/-- Underlying inverse map of iterated slice pullback comparison. -/
def overPullbackCompInv {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullback g).obj ((overPullback f).obj X)).left ⟶
      ((overPullback (g ≫ f)).obj X).left :=
  ReasLibPullback.pullbackLift X.hom (g ≫ f)
    (overPullbackFst g ((overPullback f).obj X) ≫ overPullbackFst f X)
    (overPullbackSnd g ((overPullback f).obj X))
    (by
      calc
        _ = overPullbackFst g ((overPullback f).obj X) ≫
            (overPullbackFst f X ≫ X.hom) := Category.assoc _ _ _
        _ = overPullbackFst g ((overPullback f).obj X) ≫
            (overPullbackSnd f X ≫ f) :=
          congrArg (fun k ↦ overPullbackFst g ((overPullback f).obj X) ≫ k)
            (overPullback_condition f X)
        _ = (overPullbackFst g ((overPullback f).obj X) ≫ overPullbackSnd f X) ≫ f :=
          (Category.assoc _ _ _).symm
        _ = (overPullbackSnd g ((overPullback f).obj X) ≫ g) ≫ f :=
          congrArg (fun k ↦ k ≫ f) (overPullback_condition g ((overPullback f).obj X))
        _ = _ := Category.assoc _ _ _)

/-- `overPullbackCompInv` recovers the first projection of the iterated pullback. -/
theorem overPullbackCompInv_fst {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    overPullbackCompInv f g X ≫ overPullbackFst (g ≫ f) X =
      overPullbackFst g ((overPullback f).obj X) ≫ overPullbackFst f X :=
  ReasLibPullback.pullbackLift_fst _ _ _ _ _

/-- Slice pullback along a composite is the composite of slice pullbacks. -/
noncomputable def overPullbackCompIso {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') :
    overPullback (g ≫ f) ≅ overPullback f ⋙ overPullback g :=
  overPullbackIso (g ≫ f) ≪≫ Over.pullbackComp g f ≪≫
    Functor.isoWhiskerRight (overPullbackIso f).symm (Over.pullback g) ≪≫
    Functor.isoWhiskerLeft (overPullback f) (overPullbackIso g).symm

/-- The composite comparison is transported from standard slice pullback. In particular,
the comparison on the iterated pullback uses the same bridge in each slice. -/
theorem overPullbackCompIso_standard {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') :
    overPullbackCompIso f g =
      overPullbackIso (g ≫ f) ≪≫ Over.pullbackComp g f ≪≫
        Functor.isoWhiskerRight (overPullbackIso f).symm (Over.pullback g) ≪≫
        Functor.isoWhiskerLeft (overPullback f) (overPullbackIso g).symm := rfl

private theorem standardPullbackComp_fst {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((Over.pullbackComp g f).hom.app X).left ≫
      Limits.pullback.fst (Limits.pullback.snd X.hom f) g ≫
        Limits.pullback.fst X.hom f = Limits.pullback.fst X.hom (g ≫ f) := by
  have h := congrArg (fun k ↦ k.left)
    (conjugateEquiv_counit (Over.mapPullbackAdj (g ≫ f))
      ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj f)) (Over.mapComp g f).inv X)
  change ((Over.pullbackComp g f).hom.app X).left ≫
      (Limits.pullback.fst (Limits.pullback.snd X.hom f) g ≫
        Limits.pullback.fst X.hom f) =
      𝟙 _ ≫ Limits.pullback.fst X.hom (g ≫ f) at h
  simpa only [Category.assoc, Category.id_comp] using h

/-- The component of `overPullbackCompIso` is the iterated fibre-product comparison. -/
theorem overPullbackCompIso_hom_app {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullbackCompIso f g).hom.app X).left = overPullbackCompHom f g X := by
  apply (ReasLibPullback.isPullback ((overPullback f).obj X).hom g).hom_ext
  · apply (ReasLibPullback.isPullback X.hom f).hom_ext
    · change (((overPullbackCompIso f g).hom.app X).left ≫
          overPullbackFst g ((overPullback f).obj X)) ≫ overPullbackFst f X =
        (overPullbackCompHom f g X ≫ overPullbackFst g ((overPullback f).obj X)) ≫
          overPullbackFst f X
      simp only [overPullbackCompIso, Iso.trans_hom, NatTrans.comp_app, Over.comp_left,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
        Category.assoc, overPullbackIso_inv_fst, Over.pullback_map_left,
        Limits.pullback.lift_fst_assoc, overPullbackCompHom_fst_assoc,
        overPullbackCompMid_fst]
      exact (congrArg
        (fun k ↦ ((overPullbackIso (g ≫ f)).hom.app X).left ≫ k)
        (standardPullbackComp_fst f g X)).trans (overPullbackIso_hom_fst (g ≫ f) X)
    · change (((overPullbackCompIso f g).hom.app X).left ≫
          overPullbackFst g ((overPullback f).obj X)) ≫ overPullbackSnd f X =
        (overPullbackCompHom f g X ≫ overPullbackFst g ((overPullback f).obj X)) ≫
          overPullbackSnd f X
      have hc : overPullbackFst g ((overPullback f).obj X) ≫ overPullbackSnd f X =
          overPullbackSnd g ((overPullback f).obj X) ≫ g :=
        overPullback_condition g ((overPullback f).obj X)
      have h := Over.w ((overPullbackCompIso f g).hom.app X)
      change ((overPullbackCompIso f g).hom.app X).left ≫
          overPullbackSnd g ((overPullback f).obj X) = overPullbackSnd (g ≫ f) X at h
      rw [Category.assoc, hc, ← Category.assoc, h,
        overPullbackCompHom_fst, overPullbackCompMid_snd]
  · change ((overPullbackCompIso f g).hom.app X).left ≫
        overPullbackSnd g ((overPullback f).obj X) =
      overPullbackCompHom f g X ≫ overPullbackSnd g ((overPullback f).obj X)
    exact (Over.w ((overPullbackCompIso f g).hom.app X)).trans
      (overPullbackCompHom_snd f g X).symm

/-- The associativity coherence for repeated slice pullback of algebraic spaces. -/
theorem overPseudofunctor_map₂_associator
    {S : Scheme.{u}} {X₀ X₁ X₂ X₃ : (AlgebraicSpace S)ᵒᵖ}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (Cat.Hom.isoMk (overPullbackCompIso (f ≫ g).unop h.unop)).hom ≫
        (Cat.Hom.isoMk (overPullbackCompIso f.unop g.unop)).hom ▷
          (overPullback h.unop).toCatHom ≫
      (α_ (overPullback f.unop).toCatHom (overPullback g.unop).toCatHom
        (overPullback h.unop).toCatHom).hom ≫
      (overPullback f.unop).toCatHom ◁
        (Cat.Hom.isoMk (overPullbackCompIso g.unop h.unop)).inv ≫
      (Cat.Hom.isoMk (overPullbackCompIso f.unop (g ≫ h).unop)).inv =
        eqToHom rfl := sorry

/-- The left-unit coherence for slice pullback of algebraic spaces. -/
theorem overPseudofunctor_map₂_leftUnitor
    {S : Scheme.{u}} {X Y : (AlgebraicSpace S)ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (overPullbackCompIso (𝟙 X).unop f.unop)).hom ≫
        (Cat.Hom.isoMk (overPullbackIdIso X.unop)).hom ▷
          (overPullback f.unop).toCatHom ≫
      (λ_ (overPullback f.unop).toCatHom).hom = eqToHom rfl := sorry

/-- The right-unit coherence for slice pullback of algebraic spaces. -/
theorem overPseudofunctor_map₂_rightUnitor
    {S : Scheme.{u}} {X Y : (AlgebraicSpace S)ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (overPullbackCompIso f.unop (𝟙 Y).unop)).hom ≫
        (overPullback f.unop).toCatHom ◁
          (Cat.Hom.isoMk (overPullbackIdIso Y.unop)).hom ≫
      (ρ_ (overPullback f.unop).toCatHom).hom = eqToHom rfl := sorry

/-- The contravariant pseudofunctor of algebraic-space slices over `S`, with transition
functors given by `overPullback`. -/
noncomputable def overPseudofunctor (S : Scheme.{u}) :
    Pseudofunctor (LocallyDiscrete (AlgebraicSpace S)ᵒᵖ) Cat.{u + 1, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Over X.unop))
    (fun f ↦ (overPullback f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (overPullbackIdIso X.unop))
    (fun f g ↦ Cat.Hom.isoMk (overPullbackCompIso f.unop g.unop))
    overPseudofunctor_map₂_associator
    overPseudofunctor_map₂_leftUnitor
    overPseudofunctor_map₂_rightUnitor

/-- The fibre of `overPseudofunctor` at `X` is the category of algebraic spaces over `X`. -/
theorem overPseudofunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (overPseudofunctor S).obj (.mk (.op X)) = Cat.of (Over X) := rfl

/-- The action of `overPseudofunctor` on a morphism of algebraic spaces is slice pullback. -/
theorem overPseudofunctor_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((overPseudofunctor S).map f.op.toLoc).toFunctor = overPullback f := rfl

end AlgebraicGeometry.AlgebraicSpace
