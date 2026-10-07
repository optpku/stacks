module

public import stacks_project.Chap91.Lemma_91_10_4_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence obstruction for mixed-scalar module extensions of ringed topoi

On a first-order thickening of ringed topoi, a prescribed infinitesimal comparison
c : ℐ ⊗ ℱ ⟶ 𝒦 of 𝒪-modules admits an 08MB sequence if and only if the canonical
class obstruction F K c in Ext ℱ 𝒦 2 vanishes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace ModuleExtension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} (π : 𝒪' ⟶ 𝒪)
variable [hπ : IsFirstOrderThickening π]
variable [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪')]
variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]
variable (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
variable (c : moduleTensor (ideal π) F ⟶ K)

/-- Lemma 91.10.4: Let i : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪') be a first-order thickening of
ringed topoi. After identifying underlying topoi as a same-site map π : 𝒪' ⟶ 𝒪, assume
given 𝒪-modules ℱ, 𝒦 and an 𝒪-linear map c : ℐ ⊗ ℱ ⟶ 𝒦. Then there is a canonical
class obstruction F K c in Ext ℱ 𝒦 2 whose vanishing is necessary and sufficient for
the existence of a sequence 0 ⟶ 𝒦 ⟶ ℱ' ⟶ ℱ ⟶ 0 as in 91.10.0.1 with c_ℱ' = c. -/
@[stacks 08MF]
theorem obstruction_eq_zero_iff :
    obstruction π F K c = 0 ↔
      Nonempty (ModuleExtension hπ.isSquareZero F K c) := sorry

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
