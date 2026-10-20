module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable (phi : O₁ ⟶ O₂) (F P : ringedSiteModuleCategory J O₂) (k : ℕ)

/- Definition 18.34.4 (09CU): an `O₂`-module sheaf `P` is a module of principal parts of
order `k` of `F` relative to `phi` precisely when it corepresents the functor of order-`k`
differential operators out of `F`. -/
@[stacks 09CU]
#check (DifferentialOperators.functor phi F k).CorepresentableBy P

end SheafOfModules.RingedSite
