module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Lift
import StacksCheckRecall

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [IsFirstOrderThickening π]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
variable (φ : (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj F' ⟶
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj G')

/- Lemma 91.11.1: Let i : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪') be a first-order thickening of ringed
topoi. Let ℱ', 𝒢' be 𝒪'-modules. Set ℱ = i^* ℱ' and 𝒢 = i^* 𝒢'. Let φ : ℱ ⟶ 𝒢 be an
𝒪-linear map. The set of lifts of φ to an 𝒪'-linear map φ' : ℱ' ⟶ 𝒢' is, if nonempty, a
principal homogeneous space under Hom_𝒪(ℱ, ℐ 𝒢'). -/
@[stacks 08MP] #check (SheafOfModules.RingedSite.FirstOrderThickening.lift_isEmpty_or_addTorsor F' G' φ :
    IsEmpty (Lift F' G' φ) ∨
      ∃ t : AddTorsor
          ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj F' ⟶
            idealMul π G')
          (Lift F' G' φ),
        ∀ (β : F' ⟶ idealMulO' π G') (ℓ : Lift F' G' φ),
          t.toAddAction.toAddSemigroupAction.toVAdd.vadd
              ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map β) ℓ =
            Lift.vadd F' G' φ β ℓ)

end SheafOfModules.RingedSite.FirstOrderThickening
