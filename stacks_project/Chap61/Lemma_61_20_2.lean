/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.ConstantCompletion
import StacksCheckRecall

/-!
# Lemma 61.20.2

Derived pushforward and pullback for constant Noetherian coefficients, restricted to
derived-complete objects.
-/

@[expose] public section

open CategoryTheory
open RingedSite
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived
open RingedSite.Hom.ModuleDerived.ConstantCompletion
open RingedSite.ToposHom
open RingedSite.ToposHom.DerivedComplete
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.ToposHom.DerivedComplete

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JC.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [JD.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [JC.WEqualsLocallyBijective CommRingCat.{u}]
variable [JD.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify JC RingCat.{u}]
variable [HasWeakSheafify JD RingCat.{u}]
variable [HasWeakSheafify JC (Type u)]
variable [HasWeakSheafify JD (Type u)]
variable [JC.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JD.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JC.PreservesSheafification (forget RingCat.{u})]
variable [JD.PreservesSheafification (forget RingCat.{u})]
variable [HasGlobalSectionsFunctor JC (Type u)]
variable [HasGlobalSectionsFunctor JD (Type u)]
variable [∀ X : C, HasWeakSheafify (JC.over X) AddCommGrpCat.{u}]
variable [∀ X : C, (JC.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ X : D, HasWeakSheafify (JD.over X) AddCommGrpCat.{u}]
variable [∀ X : D, (JD.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (f : MorphismOfTopoiIn JC JD) (I : Ideal Λ)
variable [(SheafOfModules.restrictScalars (ofConstantRingSheaf f Λ).structureMap).IsRightAdjoint]
variable [(ofConstantRingSheaf f Λ).HasModulePushforwardDerived]
variable [(ofConstantRingSheaf f Λ).HasModulePullbackDerived]

/- Lemma 61.20.2 (1): Derived pushforward preserves completeness. -/
@[stacks 099N] #check (RingedSite.ToposHom.DerivedComplete.pushforward_mapsDerivedComplete f I :
    derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JD I) ≤
      (derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JC I)).inverseImage
        (modulePushforwardDerived (ofConstantRingSheaf f Λ)))

/- Lemma 61.20.2 (2): Completed pullback is left adjoint to restricted pushforward. -/
@[stacks 099N] #check (RingedSite.ToposHom.DerivedComplete.completedPullback_adjunction f I :
    Nonempty (completedPullback f I ⊣ completedPushforward f I))

/- Lemma 61.20.2 (3): Derived pushforward commutes with completion. -/
@[stacks 099N] #check (RingedSite.ToposHom.DerivedComplete.pushforward_map_isDerivedCompletion f I :
    ∀ {K Khat : RingedSiteDerived JD (constantRingSheaf JD Λ)} (η : K ⟶ Khat),
      IsDerivedCompletion.{u, u, u, u} (constantIdealSheaf JD I) η →
        IsDerivedCompletion.{u, u, u, u} (constantIdealSheaf JC I)
          ((modulePushforwardDerived (ofConstantRingSheaf f Λ)).map η))

/- Lemma 61.20.2 (4): Pushforward is the homotopy limit of the pushed-forward quotient tensor tower. -/
@[stacks 099N] #check (RingedSite.ToposHom.DerivedComplete.pushforward_isHomotopyLimit_completionQuotientTower f I :
    ∀ (K : RingedSiteDerived JD (constantRingSheaf JD Λ)),
      IsDerivedCompleteWithRespectTo.{u, u, u, u} K (constantIdealSheaf JD I) →
        HomotopyLimit.IsOf
          (completionQuotientTower (constantIdealSheaf JD I) K ⋙
            modulePushforwardDerived (ofConstantRingSheaf f Λ))
          ((modulePushforwardDerived (ofConstantRingSheaf f Λ)).obj K))

/- Lemma 61.20.2 (5): Completed pullback is the homotopy limit of the pulled-back quotient tensor tower. -/
@[stacks 099N] #check (RingedSite.ToposHom.DerivedComplete.completedPullback_isHomotopyLimit_completionQuotientTower f I :
    ∀ (M : (derivedCompleteObjectProperty.{u, u, u, u}
      (constantIdealSheaf JC I)).FullSubcategory),
      HomotopyLimit.IsOf
        (completionQuotientTower (constantIdealSheaf JC I) M.obj ⋙
          modulePullbackDerived (ofConstantRingSheaf f Λ))
        ((completedPullback f I).obj M).obj)

end RingedSite.ToposHom.DerivedComplete
