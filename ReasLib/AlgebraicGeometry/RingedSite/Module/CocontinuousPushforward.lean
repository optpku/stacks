/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory

noncomputable section

universe u z

namespace RingedSite.Cocontinuous

variable {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
variable (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
variable (f : C' ⥤ D') [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
variable (R : Sheaf J' RingCat.{u}) (S : Sheaf K' RingCat.{u})
variable (α : R ⟶ (f.sheafPushforwardContinuous RingCat.{u} J' K').obj S)
variable [h_coeff : IsIso α]
variable [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
variable [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasPointwiseRightKanExtension P]
variable [(f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').Additive]
variable [(f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').Additive]
variable [PreservesFiniteLimits (SheafOfModules.pushforward.{z} α)]
variable [PreservesFiniteColimits (SheafOfModules.pushforward.{z} α)]

/-- Cocontinuous abelian pushforward of the underlying abelian sheaf of a module
sheaf. -/
abbrev modulePushforward.underlying (G : SheafOfModules.{z} R) :
    Sheaf K' AddCommGrpCat.{z} :=
  (f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').obj
    ((SheafOfModules.toSheaf R).obj G)

/-- The value of cocontinuous abelian pushforward at an object of the target
site. -/
abbrev modulePushforward.objUnderlying
    (G : SheafOfModules.{z} R) (y : D'ᵒᵖ) :
    AddCommGrpCat.{z} :=
  (modulePushforward.underlying J' K' f R G).obj.obj y

/-- The ring homomorphism `S(y) ⟶ R(x)` along a comma object, using the inverse
of the coefficient isomorphism. -/
def modulePushforward.coefficientMap (y : D'ᵒᵖ)
    (s : StructuredArrow y f.op) :
    S.obj.obj y ⟶ R.obj.obj s.right :=
  S.obj.map s.hom ≫ (inv α).hom.app s.right

/-- Scalar multiplication by a section of `S` on the underlying abelian group of
`f_* G` at `y`. -/
def modulePushforward.smulHom
    (G : SheafOfModules.{z} R) (y : D'ᵒᵖ) (r : S.obj.obj y) :
    modulePushforward.objUnderlying J' K' f R G y ⟶
      modulePushforward.objUnderlying J' K' f R G y :=
  let L := f.op
  let P := ((SheafOfModules.toSheaf R).obj G).obj
  let e := L.ranObjObjIsoLimit P y
  let D := StructuredArrow.proj y L ⋙ P
  limit.lift D
      { pt := (L.ran.obj P).obj y
        π :=
          { app := fun s ↦
              e.hom ≫
                limit.π D s ≫
                  (G.val.obj s.right).smul
                    ((modulePushforward.coefficientMap J' K' f R S α y s).hom r)
            naturality := sorry } } ≫
    e.inv

/-- The `S(y)`-module structure on the underlying abelian group of `f_* G` at
`y`. -/
@[reducible]
def modulePushforward.objModule
    (G : SheafOfModules.{z} R) (y : D'ᵒᵖ) :
    Module (S.obj.obj y)
      (modulePushforward.objUnderlying J' K' f R G y) where
  smul r a := (modulePushforward.smulHom J' K' f R S α G y r).hom a
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The value of underived cocontinuous module pushforward at an object of the
target site. -/
def modulePushforward.obj
    (G : SheafOfModules.{z} R) (y : D'ᵒᵖ) :
    ModuleCat.{z} (S.obj.obj y) :=
  @ModuleCat.of _ _ (modulePushforward.objUnderlying J' K' f R G y)
    inferInstance (modulePushforward.objModule J' K' f R S α G y)

/-- Restriction maps of underived cocontinuous module pushforward. -/
def modulePushforward.restrictionMap
    (G : SheafOfModules.{z} R) {y y' : D'ᵒᵖ} (β : y ⟶ y') :
    modulePushforward.obj J' K' f R S α G y ⟶
      (ModuleCat.restrictScalars (S.obj.map β).hom).obj
        (modulePushforward.obj J' K' f R S α G y') :=
  ConcreteCategory.ofHom (C := ModuleCat _)
    { toFun :=
        ((modulePushforward.underlying J' K' f R G).obj.map β).hom
      map_add' :=
        map_add
          ((modulePushforward.underlying J' K' f R G).obj.map β).hom
      map_smul' := sorry }

/-- The underived cocontinuous module pushforward as a presheaf of modules. -/
def modulePushforward.presheaf (G : SheafOfModules.{z} R) :
    PresheafOfModules.{z} S.obj where
  obj y := modulePushforward.obj J' K' f R S α G y
  map β := modulePushforward.restrictionMap J' K' f R S α G β
  map_id := sorry
  map_comp := sorry

/-- The underived cocontinuous module pushforward `f_*` on sheaves of modules. -/
def modulePushforward :
    SheafOfModules.{z} R ⥤ SheafOfModules.{z} S where
  obj G :=
    { val := modulePushforward.presheaf J' K' f R S α G
      isSheaf := sorry }
  map {G G'} φ :=
    { val :=
        { app := fun y ↦
            ConcreteCategory.ofHom (C := ModuleCat _)
              { toFun :=
                  (((f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').map
                        ((SheafOfModules.toSheaf R).map φ)).hom.app y).hom
                map_add' :=
                  map_add
                    (((f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').map
                          ((SheafOfModules.toSheaf R).map φ)).hom.app y).hom
                map_smul' := sorry }
          naturality := sorry } }
  map_id := sorry
  map_comp := sorry

/-- Cocontinuous module pushforward is additive. -/
instance modulePushforward.additive :
    (modulePushforward J' K' f R S α).Additive :=
  sorry

/-- The unit of the underived module inverse-image/pushforward adjunction. -/
def modulePushforward.unit :
    𝟭 (SheafOfModules.{z} S) ⟶
      SheafOfModules.pushforward.{z} α ⋙
        modulePushforward J' K' f R S α where
  app N :=
    { val :=
        { app := fun y ↦
            ConcreteCategory.ofHom (C := ModuleCat _)
              { toFun :=
                  ((f.sheafAdjunctionCocontinuous AddCommGrpCat.{z} J' K').unit.app
                        ((SheafOfModules.toSheaf S).obj N)).hom.app y |>.hom
                map_add' := sorry
                map_smul' := sorry }
          naturality := sorry } }
  naturality := sorry

/-- The counit of the underived module inverse-image/pushforward adjunction. -/
def modulePushforward.counit :
    modulePushforward J' K' f R S α ⋙
        SheafOfModules.pushforward.{z} α ⟶
      𝟭 (SheafOfModules.{z} R) where
  app M :=
    { val :=
        { app := fun x ↦
            ConcreteCategory.ofHom (C := ModuleCat _)
              { toFun :=
                  ((f.sheafAdjunctionCocontinuous AddCommGrpCat.{z} J' K').counit.app
                        ((SheafOfModules.toSheaf R).obj M)).hom.app x |>.hom
                map_add' := sorry
                map_smul' := sorry }
          naturality := sorry } }
  naturality := sorry

/-- Coefficient module inverse image is left adjoint to cocontinuous module
pushforward. -/
def modulePushforward.adjunction :
    SheafOfModules.pushforward.{z} α ⊣
      modulePushforward J' K' f R S α :=
  Adjunction.mkOfUnitCounit
    { unit := modulePushforward.unit J' K' f R S α
      counit := modulePushforward.counit J' K' f R S α
      left_triangle := sorry
      right_triangle := sorry }


end RingedSite.Cocontinuous
