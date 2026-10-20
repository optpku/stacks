module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Resolution
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.InjectiveTarget.Existence
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v w

section General

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J RingCat.{max u v})

/- Theorem 19.8.4 (1): sheaves of `𝒪`-modules on a ringed site have enough injectives. -/
@[stacks 01DU] #check
  (inferInstance : EnoughInjectives (SheafOfModules.{max u v} 𝒪))

/- Theorem 19.8.4 (2): the injective embeddings can be chosen functorially. -/
@[stacks 01DU] #check
  (inferInstance : HasFunctorialInjectives
    (SheafOfModules.{max u v} 𝒪))

end General

section AbelianDual

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v w} AddCommGrpCat.{max u v w})]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
variable (𝒪 : Sheaf J CommRingCat.{max u v w})
variable [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J 𝒪)]

/- An injective abelian sheaf which separates module maps makes the flat-bidual construction
from Lemmas 19.8.1--19.8.3 into an explicit commutative-ring specialization. -/
#check
  fun (𝒥 : AbelianDual.InjectiveTarget 𝒪) ↦
    (AbelianDual.Resolution.ofTarget 𝒥 :
      HasFunctorialInjectives
        (ringedSiteModuleCategory.{u, v, max u v w, max u v w} J 𝒪))

/- A coseparator is a stronger, reusable sufficient hypothesis for the separating condition in
the preceding construction. -/
#check fun (𝒥 : InjectiveCoseparator (Sheaf J AddCommGrpCat.{max u v w})) ↦
  (AbelianDual.Resolution.ofTarget
      (AbelianDual.InjectiveTarget.ofCoseparator 𝒪 𝒥) :
    HasFunctorialInjectives
      (ringedSiteModuleCategory.{u, v, max u v w, max u v w} J 𝒪))

#check @SheafOfModules.isGrothendieckAbelian
#check @SheafOfModules.hasFunctorialInjectives
#check @AbelianDual.InjectiveTarget.nonempty

end AbelianDual
