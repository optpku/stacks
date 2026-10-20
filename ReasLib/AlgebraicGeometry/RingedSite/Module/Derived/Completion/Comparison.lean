/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor.Unit
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ConstantCompletion
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionMap
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition

/-!
# Comparing derived completion with the quotient tensor tower
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite

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

/-- The canonical morphism from a derived module complex to its tensor product with the
structure-module quotient by an ideal power. -/
def completionQuotientMap
    (I : Subobject (unitModule J O)) (K : RingedSiteDerived J O) (n : ℕ) :
    K ⟶ ConstantCompletion.completionQuotientStage I K n :=
  (derivedTensorLeftUnitIso K).inv ≫
    (derivedTensorLeft K).map
      ((DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).map
        (IdealSheaf.PowerQuotientModule.projection I (unitModule J O) n))

/-- The quotient tensor map has a universal factor through any derived completion whenever
its quotient tensor target is derived complete. -/
def completionQuotientFactor
    (I : Subobject (unitModule J O))
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η) (n : ℕ)
    (hstage : IsDerivedCompleteWithRespectTo.{u, u, u, u}
      (ConstantCompletion.completionQuotientStage I K n) I) :
    Khat ⟶ ConstantCompletion.completionQuotientStage I K n :=
  (IsDerivedCompletion.homEquiv I hη hstage).symm (completionQuotientMap I K n)

/-- A derived tensor quotient by a positive power of a finite-type ideal sheaf is derived
complete with respect to that ideal. -/
@[stacks 0CQH]
theorem completionQuotientStage_isDerivedComplete
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K : RingedSiteDerived J O) (n : ℕ) (hn : 1 ≤ n) :
    IsDerivedCompleteWithRespectTo.{u, u, u, u}
      (ConstantCompletion.completionQuotientStage I K n) I := sorry

/-- The canonical quotient tensor maps commute with the quotient transition morphisms. -/
theorem completionQuotientMap_comp_step
    (I : Subobject (unitModule J O)) (K : RingedSiteDerived J O) (n : ℕ) :
    completionQuotientMap I K (n + 1) ≫
      ConstantCompletion.completionQuotientStep I K n =
        completionQuotientMap I K n := sorry

/-- The universal factor through derived completion recovers the positive quotient tensor
map after precomposition with the completion morphism. -/
@[stacks 0CQH]
theorem completionQuotientFactor_fac
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η) (n : ℕ) (hn : 1 ≤ n) :
    η ≫ completionQuotientFactor I K Khat η hη n
        (completionQuotientStage_isDerivedComplete I K n hn) =
      completionQuotientMap I K n := sorry

/-- Factoring a positive quotient tensor map through a derived completion is unique. -/
theorem completionQuotientMap_factor_unique
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η) (n : ℕ) (hn : 1 ≤ n)
    {φ ψ : Khat ⟶ ConstantCompletion.completionQuotientStage I K n}
    (hφ : η ≫ φ = completionQuotientMap I K n)
    (hψ : η ≫ ψ = completionQuotientMap I K n) : φ = ψ := sorry

/-- The canonical factors of positive quotient tensor maps through derived completion commute
with the quotient transitions. -/
@[stacks 0CQH]
theorem completionQuotientMap_factor_compatible
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η) (n : ℕ) (hn : 1 ≤ n) :
    completionQuotientFactor I K Khat η hη (n + 1)
        (completionQuotientStage_isDerivedComplete I K (n + 1) (Nat.succ_le_succ (Nat.zero_le n))) ≫
      ConstantCompletion.completionQuotientStep I K n =
    completionQuotientFactor I K Khat η hη n
        (completionQuotientStage_isDerivedComplete I K n hn) := sorry

/-- A derived completion maps to every presented homotopy limit of the positive quotient
tensor tower, with projections given by the canonical universal factors. -/
@[stacks 0CQH]
theorem completion_comparison_to_homotopyLimit
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat L : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η)
    (P : HomotopyLimit.Presentation (ConstantCompletion.completionQuotientTower I K) L) :
    ∃ comparison : Khat ⟶ L, ∀ n : ℕ,
      comparison ≫ P.stageProjection n =
        completionQuotientFactor I K Khat η hη (n + 1)
          (completionQuotientStage_isDerivedComplete I K (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n))) := sorry

end RingedSite.Hom.ModuleDerived
