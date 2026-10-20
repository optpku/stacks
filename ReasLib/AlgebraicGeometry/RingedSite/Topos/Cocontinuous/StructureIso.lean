module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous

/-!
# Structure-ring isomorphism for cocontinuous inverse image

An isomorphism of the restricted ring presheaf with the source structure
presheaf supplies an actual backward map through the sheafification unit.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Cocontinuous

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (G : X ⥤ Y) [G.IsCocontinuous X.siteTopology Y.siteTopology]
variable [HasSheafify X.siteTopology (Type w)]
variable [∀ P : Xᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension P]
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

/-- Re-bundle that actual backward function with the ring laws of the specified
presheaf isomorphism and the canonical inverse-image comparison. -/
def structureMapInv :
    X.structureSheaf ⟶ (toTopos G).ringInverseImage.obj Y.structureSheaf where
  hom :=
    { app := fun U ↦
        let source : RingCat.{w} := X.structureSheaf.obj.obj U
        let target : RingCat.{w} := ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U
        @RingCat.ofHom source target source.ring target.ring
          { toFun := (structureMapInverseUnderlying G e).hom.app U
            map_one' := sorry
            map_mul' := sorry
            map_zero' := sorry
            map_add' := sorry }
      naturality := sorry }

/-- The original cocontinuous structure map with the specified actual inverse. -/
def structureMapIso :
    (toTopos G).ringInverseImage.obj Y.structureSheaf ≅ X.structureSheaf where
  hom := structureMap G e.hom
  inv := structureMapInv G e
  hom_inv_id := sorry
  inv_hom_id := sorry

@[simp]
theorem structureMapIso_hom : (structureMapIso G e).hom = structureMap G e.hom := rfl

@[simp]
theorem structureMapIso_inv : (structureMapIso G e).inv = structureMapInv G e := rfl

/-- The reverse ring-map function is exactly the sheafification-unit function
of the given presheaf inverse. -/
@[simp]
theorem structureMapInv_app (U : Xᵒᵖ) (r : X.structureSheaf.obj.obj U) :
    ((structureMapInv G e).hom.app U).hom r =
      (structureMapInverseUnderlying G e).hom.app U r := rfl

end RingedSite.Cocontinuous
