module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Decomposition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homogeneous exterior-algebra inclusions and localization

This leaf records compatibility of the homogeneous decomposition with restriction to a slice.
The underlying exterior-algebra and exterior-power localization isomorphisms remain independent
of the decomposition API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v}) (U : C)
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Localization carries every homogeneous exterior-power inclusion to the corresponding
homogeneous inclusion on the slice. -/
@[stacks 01CF "localized homogeneous exterior-algebra inclusion"]
theorem powerι_overIso_hom (F : ringedSiteModuleCategory J O) (n : ℕ) :
    SheafOfModules.Hom.over (powerι O F n) U ≫ (overIso O U F).hom =
      (ExteriorPower.overIso O U F n).hom ≫ powerι (O.over U) (F.over U) n := sorry

end SheafOfModules.RingedSite.ExteriorAlgebra
