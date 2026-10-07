module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# First exterior powers and localization

This leaf records the compatibility between the degree-one exterior-power comparison and
restriction to a slice.  The degreewise localization isomorphism remains owned by
`ExteriorPower.Localization`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v}) (U : C)
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- In degree one, the localization comparison carries the restricted ambient degree-one map
to the degree-one map on the slice. -/
@[stacks 01CF "localized first exterior power"]
theorem degreeOne_overIso_hom (F : ringedSiteModuleCategory J O) :
    SheafOfModules.Hom.over (degreeOne O F) U ≫ (overIso O U F 1).hom =
      degreeOne (O.over U) (F.over U) := sorry

end SheafOfModules.RingedSite.ExteriorPower
