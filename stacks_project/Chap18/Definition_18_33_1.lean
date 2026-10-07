module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation
import StacksCheckRecall

/-! # Definition 18.33.1 compatibility entry point -/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped RelativeDerivation

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}} (phi : O₁ ⟶ O₂)
variable (F : ringedSiteModuleCategory J O₂)

/- Definition 18.33.1 (04BK): `Der[phi ; F]` is the canonical type of
relative derivations from `O₂` to the `O₂`-module sheaf `F`. -/
@[stacks 04BK]
#check (show Type _ from Der[phi ; F])

/- The notation is a thin view of the presheaf-level derivation owner. -/
#check (show Type _ from SheafOfModules.RelativeDerivation phi F)
#check PresheafOfModules.Derivation'
