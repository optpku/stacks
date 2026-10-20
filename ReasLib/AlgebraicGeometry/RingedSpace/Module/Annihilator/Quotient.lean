module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient.Module
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotient modules from annihilator containment

The generic quotient-module construction is phrased using sectionwise annihilation on a ringed
site.  For modules on a ringed space, the source-facing hypothesis is instead the subobject
containment `I ≤ Ann(F)`.  This file is the bridge between those two interfaces.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.IdealSheaf
open SheafOfModules.RingedSite.IdealSheaf.Quotient
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf

variable {X : RingedSpace.{u}}

/-- Containment in the annihilator subobject is equivalent to sectionwise annihilation. -/
@[stacks 0H2K "annihilator-containment criterion"]
theorem le_annihilator_iff
    (I : Subobject (unitModule (Opens.grothendieckTopology X) X.sheaf))
    (F : X.Modules) :
    I ≤ SheafOfModules.Annihilator.subobject F ↔ IsAnnihilated I F := sorry

/-- The annihilator ideal sheaf acts trivially on its defining module sheaf. -/
@[stacks 0H2K "annihilator acts trivially"]
theorem annihilator_isAnnihilated (F : X.Modules) :
    IsAnnihilated (J := Opens.grothendieckTopology X) (O := X.sheaf)
      (SheafOfModules.Annihilator.subobject F) F := sorry

namespace Quotient

/-- The canonical module over `O / I` obtained directly from `I ≤ Ann(F)`. -/
@[stacks 0H2K "descent from annihilator containment"]
noncomputable abbrev descendOfLE
    (I : Subobject (unitModule (Opens.grothendieckTopology X) X.sheaf))
    (F : X.Modules) (h : I ≤ SheafOfModules.Annihilator.subobject F) :
    ringedSiteModuleCategory.{u, u, u, u} (Opens.grothendieckTopology X)
      (IdealSheaf.Quotient.sheaf (J := Opens.grothendieckTopology X)
        (O := X.sheaf) I) :=
  descend I F ((le_annihilator_iff I F).1 h)

/-- The canonical module over `O / Ann(F)` carried by `F`. -/
@[stacks 0H2K "module over the annihilator quotient"]
noncomputable abbrev descendAnnihilator (F : X.Modules) :
    ringedSiteModuleCategory.{u, u, u, u} (Opens.grothendieckTopology X)
      (IdealSheaf.Quotient.sheaf (J := Opens.grothendieckTopology X)
        (O := X.sheaf) (SheafOfModules.Annihilator.subobject F)) :=
  descend (SheafOfModules.Annihilator.subobject F) F
    (annihilator_isAnnihilated F)

/-- The descended module obtained from `I ≤ Ann(F)` has the original underlying additive
sheaf. -/
@[stacks 0H2K "underlying sheaf from annihilator containment"]
noncomputable abbrev forgetIsoOfLE
    (I : Subobject (unitModule (Opens.grothendieckTopology X) X.sheaf))
    (F : X.Modules) (h : I ≤ SheafOfModules.Annihilator.subobject F) :
    (SheafOfModules.toSheaf.{u}
      (IdealSheaf.Quotient.ringSheaf (J := Opens.grothendieckTopology X)
        (O := X.sheaf) I)).obj (descendOfLE I F h) ≅
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F :=
  forgetIso I F ((le_annihilator_iff I F).1 h)

/-- The module over `O / Ann(F)` has the same underlying additive sheaf as `F`. -/
@[stacks 0H2K "underlying sheaf over the annihilator quotient"]
noncomputable abbrev forgetIsoAnnihilator (F : X.Modules) :
    (SheafOfModules.toSheaf.{u}
      (IdealSheaf.Quotient.ringSheaf (J := Opens.grothendieckTopology X)
        (O := X.sheaf) (SheafOfModules.Annihilator.subobject F))).obj
          (descendAnnihilator F) ≅
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F :=
  forgetIso (SheafOfModules.Annihilator.subobject F) F
    (annihilator_isAnnihilated F)

/-- Pulling the descended scalar action back along `O ⟶ O / I` recovers the original action. -/
@[stacks 0H2K "scalar action from annihilator containment"]
theorem smul_projection_of_le
    (I : Subobject (unitModule (Opens.grothendieckTopology X) X.sheaf))
    (F : X.Modules) (h : I ≤ SheafOfModules.Annihilator.subobject F)
    (U : (Opens X)ᵒᵖ) (r : X.presheaf.obj U) (m : F.val.obj U) :
    (forgetIsoOfLE I F h).hom.hom.app U
        (((CategoryTheory.toSheafify
          (Opens.grothendieckTopology X)
          (IdealSheaf.Quotient.presheaf (J := Opens.grothendieckTopology X)
            (O := X.sheaf) I)).app U).hom
            (sectionProjection I U r) •
          unitApp I F ((le_annihilator_iff I F).1 h) U m) =
      r • m := sorry

end Quotient

end AlgebraicGeometry.RingedSpace.IdealSheaf
