/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_6_8
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Morphism.Existence

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
variable [MonoidalCategory (RingedSiteDerived J O)]

/-! The quotient stages and their transition maps are kept explicit so that the
source-facing remark can refer to the actual derived tensor tower. -/

/-- Derived tensor stage `K ⊗ᴸ_O O / I^n`. -/
noncomputable abbrev completionQuotientStage
    (I : Subobject (unitModule J O)) (K : RingedSiteDerived J O) (n : ℕ) :
    RingedSiteDerived J O :=
  K ⊗ (DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).obj
    (IdealSheaf.PowerQuotientModule.stage I (unitModule J O) n)

/-- The derived transition map from the `(n + 1)`st quotient stage to the `n`th stage. -/
noncomputable def completionQuotientStep
    (I : Subobject (unitModule J O)) (K : RingedSiteDerived J O) (n : ℕ) :
    completionQuotientStage I K (n + 1) ⟶ completionQuotientStage I K n :=
  𝟙 K ⊗ₘ
    (DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).map
      (IdealSheaf.PowerQuotientModule.step I (unitModule J O) n)

/-- The inverse tower of derived tensor quotients. -/
noncomputable abbrev completionQuotientTower
    (I : Subobject (unitModule J O)) (K : RingedSiteDerived J O) :
    ℕᵒᵖ ⥤ RingedSiteDerived J O :=
  @Functor.ofOpSequence (RingedSiteDerived J O) _
    (fun n ↦ completionQuotientStage I K (n + 1))
    (fun n ↦ completionQuotientStep I K (n + 1))

/-- The canonical map from `K` to the derived tensor quotient at stage `n`. -/
noncomputable def completionQuotientMap
    (I : Subobject (unitModule J O)) (K : RingedSiteDerived J O)
    (s : (DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).obj
      (unitModule J O) ≅ 𝟙_ (RingedSiteDerived J O)) (n : ℕ) :
    K ⟶ completionQuotientStage I K n :=
  (ρ_ K).inv ≫
    (𝟙 K ⊗ₘ
      (s.inv ≫
        (DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).map
          (IdealSheaf.PowerQuotientModule.projection I (unitModule J O) n)))

/-- The canonical factor of the quotient map through a chosen derived completion. -/
noncomputable def completionQuotientFactor
    (I : Subobject (unitModule J O))
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η)
    (s : (DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).obj
      (unitModule J O) ≅ 𝟙_ (RingedSiteDerived J O))
    (n : ℕ)
    (hstage : IsDerivedCompleteWithRespectTo.{u, u, u, u}
      (completionQuotientStage I K n) I) :
    Khat ⟶ completionQuotientStage I K n :=
  (IsDerivedCompletion.homEquiv I hη hstage).symm (completionQuotientMap I K s n)

/-- Remark 52.6.13 (Comparison with completion) (1): the derived tensor quotient stage is
derived complete for every positive power. -/
@[stacks 0CQH]
theorem completionQuotientStage_isDerivedComplete
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K : RingedSiteDerived J O) (n : ℕ) (hn : 1 ≤ n) :
    IsDerivedCompleteWithRespectTo.{u, u, u, u} (completionQuotientStage I K n) I := sorry

/-- Remark 52.6.13 (Comparison with completion) (2): the canonical map to a positive quotient
factors through the derived completion. -/
@[stacks 0CQH]
theorem completionQuotientFactor_fac
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η)
    (s : (DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).obj
      (unitModule J O) ≅ 𝟙_ (RingedSiteDerived J O))
    (n : ℕ) (hn : 1 ≤ n)
    (hstage : IsDerivedCompleteWithRespectTo.{u, u, u, u}
      (completionQuotientStage I K n) I) :
    η ≫ completionQuotientFactor I K Khat η hη s n hstage =
      completionQuotientMap I K s n := sorry

/-- The factorization through completion is unique by the derived-completion universal property. -/
theorem completionQuotientMap_factor_unique
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η)
    (s : (DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).obj
      (unitModule J O) ≅ 𝟙_ (RingedSiteDerived J O))
    (n : ℕ) (hn : 1 ≤ n) {φ ψ : Khat ⟶ completionQuotientStage I K n}
    (hφ : η ≫ φ = completionQuotientMap I K s n)
    (hψ : η ≫ ψ = completionQuotientMap I K s n) :
    φ = ψ := sorry

/-- Remark 52.6.13 (Comparison with completion) (3): the quotient-stage factorizations are
compatible with the transition maps in the inverse tower. -/
@[stacks 0CQH]
theorem completionQuotientMap_factor_compatible
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η)
    (s : (DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).obj
      (unitModule J O) ≅ 𝟙_ (RingedSiteDerived J O))
    (n : ℕ) (hn : 1 ≤ n)
    (hstage : IsDerivedCompleteWithRespectTo.{u, u, u, u}
      (completionQuotientStage I K n) I)
    (hstage_succ : IsDerivedCompleteWithRespectTo.{u, u, u, u}
      (completionQuotientStage I K (n + 1)) I) :
    completionQuotientFactor I K Khat η hη s (n + 1) hstage_succ ≫
        completionQuotientStep I K n =
      completionQuotientFactor I K Khat η hη s n hstage := sorry

/-- Remark 52.6.13 (Comparison with completion) (4): a compatible family induces the comparison
from the derived completion to a homotopy limit of the quotient tower. The statement deliberately
does not assert that this comparison is an isomorphism, since such comparisons need not be
isomorphisms in general. -/
@[stacks 0CQH]
theorem completion_comparison_to_homotopyLimit
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K Khat L : RingedSiteDerived J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η)
    (s : (DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).obj
      (unitModule J O) ≅ 𝟙_ (RingedSiteDerived J O))
    (P : HomotopyLimit.Presentation (completionQuotientTower I K) L)
    (φ : ∀ n : ℕ, Khat ⟶ (completionQuotientTower I K).obj (op n))
    (hφ : ∀ n : ℕ, η ≫ φ n = completionQuotientMap I K s (n + 1))
    (hcompat : ∀ n : ℕ,
      φ (n + 1) ≫ completionQuotientStep I K (n + 1) = φ n) :
    ∃ comparison : Khat ⟶ L, ∀ n : ℕ,
      comparison ≫ P.stageProjection n = φ n := sorry

end RingedSite.Hom.ModuleDerived
