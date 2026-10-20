module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

/-!
# Flat morphisms of ringed topoi

Flatness is exactness of extension of scalars along the inverse-image structure map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite

universe uX vX uY vY w

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (f : ToposHom X Y)
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]

#check (ToposHom.isFlat_iff_extendScalars_exact f :
  ToposHom.IsFlat f ↔
    exactFunctor
      (SheafOfModules.{w} (f.toTopos.ringInverseImage.obj Y.structureSheaf))
      (SheafOfModules.{w} X.structureSheaf)
      (SheafOfModules.ChangeOfRings.extendScalars f.structureMap))
