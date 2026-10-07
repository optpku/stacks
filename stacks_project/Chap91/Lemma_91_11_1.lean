module

public import Mathlib.Algebra.Torsor.Defs
public import stacks_project.Chap91.Lemma_91_11_1_IdealMul
public import stacks_project.Chap91.Lemma_91_11_1_Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifts of maps of modules on a first-order thickening of ringed topoi

On a first-order thickening of ringed topoi, after identifying underlying topoi, the type of
𝒪'-linear lifts of an 𝒪-linear map φ : i^* ℱ' ⟶ i^* 𝒢' is, if nonempty, a principal homogeneous
space under Hom_𝒪(ℱ, ℐ 𝒢').
-/

@[expose] public section

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

/-- Lemma 91.11.1: Let i : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪') be a first-order thickening of ringed
topoi. Let ℱ', 𝒢' be 𝒪'-modules. Set ℱ = i^* ℱ' and 𝒢 = i^* 𝒢'. Let φ : ℱ ⟶ 𝒢 be an
𝒪-linear map. The set of lifts of φ to an 𝒪'-linear map φ' : ℱ' ⟶ 𝒢' is, if nonempty, a
principal homogeneous space under Hom_𝒪(ℱ, ℐ 𝒢'). -/
@[stacks 08MP]
theorem lift_isEmpty_or_addTorsor :
    IsEmpty (Lift F' G' φ) ∨
      Nonempty
        (AddTorsor
          ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj F' ⟶
            idealMul π G')
          (Lift F' G' φ)) :=
  sorry

end SheafOfModules.RingedSite.FirstOrderThickening

