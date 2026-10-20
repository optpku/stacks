module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GlobalSections

/-- The category of `𝒪_X`-modules is canonically linear over the scheme-theoretic global
section ring `Scheme.globalSectionsRing X`. -/
noncomputable instance instLinearModules (X : Scheme.{u}) :
    Linear (Scheme.globalSectionsRing X) X.toRingedSpace.Modules :=
  Linear.ofRingMorphism
    ((RingedSpace.GlobalSections.centerHom X.toRingedSpace).comp
      (eqToHom (SheafedSpace.Γ_obj_op X.toRingedSpace).symm).hom)

/-- Scheme modules inherit the canonical action of the ringed-space global section ring. -/
noncomputable instance instLinearSchemeModules (X : Scheme.{u}) :
    Linear (RingedSpace.globalSectionsRing X.toRingedSpace) X.Modules :=
  RingedSpace.GlobalSections.instLinear X.toRingedSpace

end AlgebraicGeometry.Scheme.GlobalSections
