module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.FirstOrder.Truncation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts.FirstOrder

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂)
variable [HasSheafify J AddCommGrpCat.{max u v}]

/- Lemma 18.34.6 (09CW): the canonical sequence
`Ω_{O₂/O₁} ⊗_{O₂} F ⟶ P¹_{O₂/O₁}(F) ⟶ F` is short exact and is
functorial in `F`. -/
@[stacks 09CW]
#check (shortExact phi F : (sequence phi F).ShortExact)
#check sequenceMap phi
#check sequenceFunctor phi

end SheafOfModules.RingedSite.PrincipalParts.FirstOrder
