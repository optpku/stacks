module

import StacksCheckRecall
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient

open CategoryTheory Opposite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (I : Subobject (unitModule J 𝒪)) (n : ℕ)

/- 31.19.1.1: the pushforward degree-`n` piece `i_* 𝒞_{Z/X,n}` of the normal cone of an
immersion with ideal sheaf `ℐ` is the intrinsic graded piece
`ker(𝒪 / ℐ ^ (n + 1) ⟶ 𝒪 / ℐ ^ n)`. -/
@[stacks 0631]
#check (SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.gradedPiece I n :
  SheafOfModules (SheafOfModules.RingedSite.ringSheaf J
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.sheaf I (n + 1))))

#check (SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.sheafTransition I n :
  SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.sheaf I (n + 1) ⟶
    SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.sheaf I n)

end SheafOfModules.RingedSite
