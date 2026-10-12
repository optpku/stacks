/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Annihilator
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.Annihilator

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable [LocallyOfFiniteType f] [LocallyQuasiFinite f]

/-- The different ideal sheaf associated to a global section of a relative dualizing sheaf. -/
noncomputable def different (W : f.RelativeDualizingSheaf)
    (τ : W.module.obj.sections) : Y.IdealSheafData :=
  Scheme.Modules.schemeTheoreticSupport
    (cokernel (W.module.obj.unitHomEquiv.symm τ))

/-- The different is the scheme-theoretic support of the cokernel of the section map. -/
theorem different_def (W : f.RelativeDualizingSheaf)
    (τ : W.module.obj.sections) :
    W.different τ = Scheme.Modules.schemeTheoreticSupport
      (cokernel (W.module.obj.unitHomEquiv.symm τ)) := sorry

/-- On an affine open, the different is the annihilator of the section-map cokernel. -/
theorem different_ideal (W : f.RelativeDualizingSheaf)
    (τ : W.module.obj.sections) (U : Y.affineOpens) :
    (W.different τ).ideal U =
      Module.annihilator Γ(Y, U) Γ(cokernel (W.module.obj.unitHomEquiv.symm τ), U) := sorry

/-- On an affine open, the different ideal is the section ideal of the annihilator
subobject of the section-map cokernel. -/
theorem different_ideal_eq_annihilator_sections
    (W : f.RelativeDualizingSheaf) (τ : W.module.obj.sections)
    (U : Y.affineOpens) :
    (W.different τ).ideal U =
      RingedSite.IdealSheaf.sections
        (Annihilator.subobject
          (cokernel (W.module.obj.unitHomEquiv.symm τ)))
        (op (U : Y.Opens)) := sorry

/-- The cokernel of the section map into a relative dualizing sheaf is coherent. -/
theorem sectionCokernel_isCoherent (W : f.RelativeDualizingSheaf)
    (τ : W.module.obj.sections) :
    IsCoherent (cokernel (W.module.obj.unitHomEquiv.symm τ)) := sorry

/-- The annihilator of the section-map cokernel is a coherent module sheaf. -/
theorem differentAnnihilator_isCoherent (W : f.RelativeDualizingSheaf)
    (τ : W.module.obj.sections) :
    IsCoherent
      (annihilator (cokernel (W.module.obj.unitHomEquiv.symm τ))) := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf
