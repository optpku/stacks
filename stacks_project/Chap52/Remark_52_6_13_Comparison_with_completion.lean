module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completion.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- The positive ideal-power quotient tensor tower, with stage `n` corresponding to
the exponent `n + 1`. -/
abbrev completionQuotientTower
    (I : Subobject (unitModule J O)) (K : RingedSiteDerived J O) :
    ℕᵒᵖ ⥤ RingedSiteDerived J O :=
  ConstantCompletion.completionQuotientTower I K

/- Remark 52.6.13 (Comparison with completion): the derived quotient tensor stages. -/
@[stacks 0CQH]
#check (RingedSite.Hom.ModuleDerived.ConstantCompletion.completionQuotientStage :
  ∀ (I : Subobject (unitModule J O)) (K : RingedSiteDerived J O) (n : ℕ),
    RingedSiteDerived J O)

/- Remark 52.6.13 (Comparison with completion): the quotient tensor transitions. -/
@[stacks 0CQH]
#check (RingedSite.Hom.ModuleDerived.ConstantCompletion.completionQuotientStep :
  ∀ (I : Subobject (unitModule J O)) (K : RingedSiteDerived J O) (n : ℕ),
    ConstantCompletion.completionQuotientStage I K (n + 1) ⟶
      ConstantCompletion.completionQuotientStage I K n)

/- Remark 52.6.13 (Comparison with completion): completionQuotientStage_isDerivedComplete. -/
@[stacks 0CQH]
#check (RingedSite.Hom.ModuleDerived.completionQuotientStage_isDerivedComplete :
  ∀ (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K : RingedSiteDerived J O) (n : ℕ) (hn : 1 ≤ n),
    IsDerivedCompleteWithRespectTo.{u, u, u, u}
      (ConstantCompletion.completionQuotientStage I K n) I)

/- Remark 52.6.13 (Comparison with completion): completionQuotientFactor_fac. -/
@[stacks 0CQH]
#check (RingedSite.Hom.ModuleDerived.completionQuotientFactor_fac :
  ∀ (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η) (n : ℕ) (hn : 1 ≤ n),
    η ≫ completionQuotientFactor I K Khat η hη n
        (completionQuotientStage_isDerivedComplete I K n hn) =
      completionQuotientMap I K n)

/- Remark 52.6.13 (Comparison with completion): completionQuotientMap_factor_unique. -/
@[stacks 0CQH]
#check (RingedSite.Hom.ModuleDerived.completionQuotientMap_factor_unique :
  ∀ (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η) (n : ℕ) (hn : 1 ≤ n)
    {φ ψ : Khat ⟶ ConstantCompletion.completionQuotientStage I K n}
    (hφ : η ≫ φ = completionQuotientMap I K n)
    (hψ : η ≫ ψ = completionQuotientMap I K n), φ = ψ)

/- Remark 52.6.13 (Comparison with completion): completionQuotientMap_factor_compatible. -/
@[stacks 0CQH]
#check (RingedSite.Hom.ModuleDerived.completionQuotientMap_factor_compatible :
  ∀ (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η) (n : ℕ) (hn : 1 ≤ n),
    completionQuotientFactor I K Khat η hη (n + 1)
        (completionQuotientStage_isDerivedComplete I K (n + 1) (Nat.succ_le_succ (Nat.zero_le n))) ≫
      ConstantCompletion.completionQuotientStep I K n =
    completionQuotientFactor I K Khat η hη n
        (completionQuotientStage_isDerivedComplete I K n hn))

/- Remark 52.6.13 (Comparison with completion) -/
@[stacks 0CQH]
#check (RingedSite.Hom.ModuleDerived.completion_comparison_to_homotopyLimit :
  ∀ (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat L : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η)
    (P : HomotopyLimit.Presentation (ConstantCompletion.completionQuotientTower I K) L),
    ∃ comparison : Khat ⟶ L, ∀ n : ℕ,
      comparison ≫ P.stageProjection n =
        completionQuotientFactor I K Khat η hη (n + 1)
          (completionQuotientStage_isDerivedComplete I K (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n))))

end RingedSite.Hom.ModuleDerived
