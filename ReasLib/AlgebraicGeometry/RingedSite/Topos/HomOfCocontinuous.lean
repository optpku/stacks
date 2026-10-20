/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe uX vX uY vY w

namespace RingedSite.Cocontinuous

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (G : X.carrier ⥤ Y.carrier) [G.IsCocontinuous X.siteTopology Y.siteTopology]
variable [HasSheafify X.siteTopology (Type w)]
variable [∀ P : X.carrierᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension P]
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (η : G.op ⋙ Y.structureSheaf.obj ⟶ X.structureSheaf.obj)

/-- The geometric morphism induced by the cocontinuous functor. -/
noncomputable abbrev toTopos : MorphismOfTopoiIn Y.siteTopology X.siteTopology :=
  G.morphismOfTopoiInOfCocontinuous X.siteTopology Y.siteTopology

/-- Sheafification extends the given ring-valued presheaf map on underlying
types. Thus the structure map is tied to actual functions on the site. -/
noncomputable def underlyingStructureMap :
    (toTopos G).inverseImage.obj (Hom.underlyingStructureSheaf Y) ⟶
      Hom.underlyingStructureSheaf X :=
  ((sheafificationAdjunction X.siteTopology (Type w)).homEquiv _ _).symm
    (Functor.whiskerRight η (forget RingCat.{w}))

/-- The same map expressed on the underlying sheaf of the canonical ring
inverse image, using its coefficient-forgetful comparison. -/
noncomputable def ringUnderlyingStructureMap :
    (sheafCompose X.siteTopology (forget RingCat.{w})).obj
        ((toTopos G).ringInverseImage.obj Y.structureSheaf) ⟶
      Hom.underlyingStructureSheaf X :=
  (toTopos G).ringInverseImageForgetIso.hom.app Y.structureSheaf ≫
    underlyingStructureMap G η

/-- The section function induced by sheafification preserves one. -/
private theorem structureMap_map_one (U : X.carrierᵒᵖ) :
    ((ringUnderlyingStructureMap G η).hom.app U)
        (1 : ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U) =
      (1 : X.structureSheaf.obj.obj U) :=
  sorry

/-- The section function induced by sheafification preserves multiplication. -/
private theorem structureMap_map_mul (U : X.carrierᵒᵖ)
    (a b : ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U) :
    ((ringUnderlyingStructureMap G η).hom.app U) (a * b) =
      (inferInstance : Mul (X.structureSheaf.obj.obj U)).mul
        (((ringUnderlyingStructureMap G η).hom.app U) a)
        (((ringUnderlyingStructureMap G η).hom.app U) b) :=
  sorry

/-- The section function induced by sheafification preserves zero. -/
private theorem structureMap_map_zero (U : X.carrierᵒᵖ) :
    ((ringUnderlyingStructureMap G η).hom.app U)
        (0 : ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U) =
      (0 : X.structureSheaf.obj.obj U) :=
  sorry

/-- The section function induced by sheafification preserves addition. -/
private theorem structureMap_map_add (U : X.carrierᵒᵖ)
    (a b : ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U) :
    ((ringUnderlyingStructureMap G η).hom.app U) (a + b) =
      (inferInstance : Add (X.structureSheaf.obj.obj U)).add
        (((ringUnderlyingStructureMap G η).hom.app U) a)
        (((ringUnderlyingStructureMap G η).hom.app U) b) :=
  sorry

/-- The structure-ring morphism induced by a presheaf ring morphism has the
section functions obtained by sheafification and the coefficient-forgetful comparison. -/
noncomputable def structureMap :
    (toTopos G).ringInverseImage.obj Y.structureSheaf ⟶ X.structureSheaf where
  hom :=
    { app := fun U ↦
        let source : RingCat.{w} := ((toTopos G).ringInverseImage.obj Y.structureSheaf).obj.obj U
        let target : RingCat.{w} := X.structureSheaf.obj.obj U
        @RingCat.ofHom source target source.ring target.ring
        { toFun := (ringUnderlyingStructureMap G η).hom.app U
          map_one' := by exact structureMap_map_one G η U
          map_mul' := by exact structureMap_map_mul G η U
          map_zero' := by exact structureMap_map_zero G η U
          map_add' := by exact structureMap_map_add G η U }
      naturality := sorry }

/-- A cocontinuous functor with its actual structure-presheaf map determines
a morphism of ringed topoi in the same geometric direction. -/
noncomputable def toRingedTopos : ToposHom X Y where
  toTopos := toTopos G
  structureMap := structureMap G η

end RingedSite.Cocontinuous
