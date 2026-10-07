module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport

/-!
# Annihilator presentation of scheme-theoretic support

The canonical scheme-theoretic support ideal is identified with the section ideal of the
annihilator subobject.
-/

@[expose] public section

open AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- On an affine open, the ideal of the scheme-theoretic support is the section ideal of the
annihilator subobject. -/
theorem schemeTheoreticSupport_ideal_eq_annihilator_sections
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (U : X.affineOpens) :
    (schemeTheoreticSupport ℱ).ideal U =
      SheafOfModules.RingedSite.IdealSheaf.sections
        (SheafOfModules.Annihilator.subobject (X := X.toRingedSpace) ℱ)
        (op (U : X.Opens)) := sorry

end AlgebraicGeometry.Scheme.Modules
