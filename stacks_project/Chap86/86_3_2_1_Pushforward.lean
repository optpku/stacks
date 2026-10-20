module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [QuasiCompact f] [QuasiSeparated f]

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn.mapsTo f :
  derivedQuasiCoherentModuleProperty X ≤
    (derivedQuasiCoherentModuleProperty Y).inverseImage (moduleDerivedPushforward f))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn f :
  DerivedQCoh X ⥤ DerivedQCoh Y)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn.inclusionIso f :
  pushforwardCohomologyIn f ⋙ inclusion Y ≅ inclusion X ⋙ moduleDerivedPushforward f)
