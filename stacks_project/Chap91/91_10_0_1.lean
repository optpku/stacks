module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Infinitesimal
import StacksCheckRecall

/-!
# Mixed-scalar extensions of modules on first-order thickenings of ringed topoi

The named equation of Stacks Tag 08MB is the short exact sequence
0 ⟶ 𝒦 ⟶ ℱ' ⟶ ℱ ⟶ 0 associated to a mixed-scalar extension on a same-site first-order
thickening π : 𝒪' ⟶ 𝒪.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}

/-91.10.0.1: 0 ⟶ 𝒦 ⟶ ℱ' ⟶ ℱ ⟶ 0. -/
@[stacks 08MB] #check (SheafOfModules.RingedSite.FirstOrderThickening.shortComplex :
  (E : Extension π) →
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪'))

#check (SheafOfModules.RingedSite.FirstOrderThickening.shortComplex_shortExact :
  (E : Extension π) →
    (SheafOfModules.RingedSite.FirstOrderThickening.shortComplex E).ShortExact)

end SheafOfModules.RingedSite.FirstOrderThickening
