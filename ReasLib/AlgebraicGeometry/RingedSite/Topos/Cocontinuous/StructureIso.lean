/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous

/-!
# Structure-ring isomorphism for cocontinuous inverse image

An isomorphism of the restricted ring presheaf with the source structure
presheaf supplies an actual backward map through the sheafification unit.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Cocontinuous

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (G : X.carrier ⥤ Y.carrier) [G.IsCocontinuous X.siteTopology Y.siteTopology]
variable [HasSheafify X.siteTopology (Type w)]
variable [∀ P : X.carrierᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension P]
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (e : G.op ⋙ Y.structureSheaf.obj ≅ X.structureSheaf.obj)

/-- The actual backward underlying sheaf map: use the supplied presheaf inverse,
then the sheafification unit and the canonical ring-forgetful comparison. -/
def structureMapInverseUnderlying :
    Hom.underlyingStructureSheaf X ⟶
      (sheafCompose X.siteTopology (forget RingCat.{w})).obj
        ((toTopos G).ringInverseImage.obj Y.structureSheaf) :=
  (show Hom.underlyingStructureSheaf X ⟶
      (toTopos G).inverseImage.obj (Hom.underlyingStructureSheaf Y) from
    ⟨Functor.whiskerRight e.inv (forget RingCat.{w}) ≫
      toSheafify X.siteTopology (G.op ⋙ Y.structureSheaf.obj ⋙ forget RingCat.{w})⟩) ≫
    (toTopos G).ringInverseImageForgetIso.inv.app Y.structureSheaf

/-- The inverse structure-map function preserves the multiplicative identity. -/
private theorem structureMapInv_map_one (U : X.carrierᵒᵖ) :
    let source : RingCat.{w} := X.structureSheaf.obj.obj U
    let target : RingCat.{w} := ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U
    let backward : source → target := (structureMapInverseUnderlying G e).hom.app U
    backward (1 : source) = (1 : target) := sorry

/-- The inverse structure-map function preserves multiplication. -/
private theorem structureMapInv_map_mul (U : X.carrierᵒᵖ) :
    let source : RingCat.{w} := X.structureSheaf.obj.obj U
    let target : RingCat.{w} := ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U
    let backward : source → target := (structureMapInverseUnderlying G e).hom.app U
    ∀ x y : source, backward (x * y) = (backward x : target) * backward y := sorry

/-- The inverse structure-map function preserves zero. -/
private theorem structureMapInv_map_zero (U : X.carrierᵒᵖ) :
    let source : RingCat.{w} := X.structureSheaf.obj.obj U
    let target : RingCat.{w} := ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U
    let backward : source → target := (structureMapInverseUnderlying G e).hom.app U
    backward (0 : source) = (0 : target) := sorry

/-- The inverse structure-map function preserves addition. -/
private theorem structureMapInv_map_add (U : X.carrierᵒᵖ) :
    let source : RingCat.{w} := X.structureSheaf.obj.obj U
    let target : RingCat.{w} := ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U
    let backward : source → target := (structureMapInverseUnderlying G e).hom.app U
    ∀ x y : source, backward (x + y) = (backward x : target) + backward y := sorry

/-- The sectionwise ring homomorphism induced by the inverse structure-map function. -/
private def structureMapInvApp (U : X.carrierᵒᵖ) :
    X.structureSheaf.obj.obj U ⟶
      ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U :=
  let source : RingCat.{w} := X.structureSheaf.obj.obj U
  let target : RingCat.{w} := ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U
  @RingCat.ofHom source target source.ring target.ring
    { toFun := (structureMapInverseUnderlying G e).hom.app U
      map_one' := structureMapInv_map_one G e U
      map_mul' := structureMapInv_map_mul G e U
      map_zero' := structureMapInv_map_zero G e U
      map_add' := structureMapInv_map_add G e U }

/-- The sectionwise inverse structure maps commute with restriction. -/
private theorem structureMapInv_naturality {U V : X.carrierᵒᵖ} (f : U ⟶ V) :
    X.structureSheaf.obj.map f ≫ structureMapInvApp G e V =
      structureMapInvApp G e U ≫
        ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.map f := sorry

/-- The inverse structure-map function, bundled as a morphism of ring sheaves. -/
def structureMapInv :
    X.structureSheaf ⟶ (toTopos G).ringInverseImage.obj Y.structureSheaf where
  hom :=
    { app := structureMapInvApp G e
      naturality := fun _ _ f ↦ structureMapInv_naturality G e f }

/-- The structure map followed by its specified inverse is the identity. -/
private theorem structureMapIso_hom_inv_id :
    structureMap G e.hom ≫ structureMapInv G e = 𝟙 _ := sorry

/-- The specified inverse followed by the structure map is the identity. -/
private theorem structureMapIso_inv_hom_id :
    structureMapInv G e ≫ structureMap G e.hom = 𝟙 _ := sorry

/-- The cocontinuous structure map is an isomorphism with its specified inverse. -/
def structureMapIso :
    (toTopos G).ringInverseImage.obj Y.structureSheaf ≅ X.structureSheaf where
  hom := structureMap G e.hom
  inv := structureMapInv G e
  hom_inv_id := structureMapIso_hom_inv_id G e
  inv_hom_id := structureMapIso_inv_hom_id G e

/-- The forward map of the structure-ring isomorphism is the structure map. -/
@[simp]
theorem structureMapIso_hom : (structureMapIso G e).hom = structureMap G e.hom := rfl

/-- The backward map of the structure-ring isomorphism is its specified inverse. -/
@[simp]
theorem structureMapIso_inv : (structureMapIso G e).inv = structureMapInv G e := rfl

/-- The reverse ring-map function is exactly the sheafification-unit function
of the given presheaf inverse. -/
@[simp]
theorem structureMapInv_app (U : X.carrierᵒᵖ) (r : X.structureSheaf.obj.obj U) :
    ((structureMapInv G e).hom.app U).hom r =
      (structureMapInverseUnderlying G e).hom.app U r := rfl

end RingedSite.Cocontinuous
