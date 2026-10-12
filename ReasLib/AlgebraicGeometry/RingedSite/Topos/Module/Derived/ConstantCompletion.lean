/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ConstantCoefficients
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Completion
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ConstantCompletion
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completion
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionMap

/-!
# Derived-complete pushforward and pullback for constant coefficients

The restriction of `Rf_*` to `D_comp(D, Λ)` and its left adjoint `Lf_comp^*`, obtained by
derived pullback followed by the canonical derived-completion reflector.
-/

@[expose] public section

open CategoryTheory
open ObjectProperty.FullSubcategory
open RingedSite
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived
open RingedSite.Hom.ModuleDerived.ConstantCompletion
open RingedSite.ToposHom
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

/-- Restricted derived pushforward `Rf_* : D_comp(D, Λ) ⥤ D_comp(C, Λ)`. -/
noncomputable abbrev completedPushforward :
    (derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JD I)).FullSubcategory ⥤
      (derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JC I)).FullSubcategory :=
  pushforward (ofConstantRingSheaf f Λ) (constantIdealSheaf JC I)
    (constantIdealSheaf JD I) (mapsConstantIdeal f I)

/-- Derived pullback on complete objects followed by derived completion,
`Lf_comp^* : D_comp(C, Λ) ⥤ D_comp(D, Λ)`. -/
noncomputable abbrev completedPullback :
    (derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JC I)).FullSubcategory ⥤
      (derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JD I)).FullSubcategory :=
  pullbackOfFiniteType (ofConstantRingSheaf f Λ)
    (constantIdealSheaf JC I) (constantIdealSheaf JD I)

/-- Forgetting completeness, restricted pushforward is ambient derived pushforward. -/
noncomputable abbrev completedPushforward_comp_inclusion :
    completedPushforward f I ⋙
        (derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JC I)).ι ≅
      (derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JD I)).ι ⋙
        modulePushforwardDerived (ofConstantRingSheaf f Λ) :=
  pushforwardCompInclusionIso (ofConstantRingSheaf f Λ) (constantIdealSheaf JC I)
    (constantIdealSheaf JD I) (mapsConstantIdeal f I)

/-- Forgetting completeness, `Lf_comp^*` is `Lf^*` followed by derived completion. -/
noncomputable abbrev completedPullback_comp_inclusion :
    completedPullback f I ⋙
        (derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JD I)).ι ≅
      (derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JC I)).ι ⋙
        modulePullbackDerived (ofConstantRingSheaf f Λ) ⋙
          (Completion.reflector (constantIdealSheaf JD I)).reflection :=
  pullbackOfFiniteTypeCompInclusionIso (ofConstantRingSheaf f Λ)
    (constantIdealSheaf JC I) (constantIdealSheaf JD I)

/-- Derived pushforward preserves derived completeness for constant Noetherian coefficients. -/
theorem pushforward_mapsDerivedComplete :
    derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JD I) ≤
      (derivedCompleteObjectProperty.{u, u, u, u} (constantIdealSheaf JC I)).inverseImage
        (modulePushforwardDerived (ofConstantRingSheaf f Λ)) := sorry

/-- Derived pullback followed by completion is left adjoint to restricted derived pushforward
for constant Noetherian coefficients. -/
theorem completedPullback_adjunction :
    Nonempty (completedPullback f I ⊣ completedPushforward f I) := sorry

/-- Derived pushforward carries every derived-completion map to a derived-completion map
for constant Noetherian coefficients. -/
theorem pushforward_map_isDerivedCompletion
    {K Khat : RingedSiteDerived JD (constantRingSheaf JD Λ)} (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} (constantIdealSheaf JD I) η) :
    IsDerivedCompletion.{u, u, u, u} (constantIdealSheaf JC I)
      ((modulePushforwardDerived (ofConstantRingSheaf f Λ)).map η) := sorry

/-- The derived pushforward of a derived-complete object is a homotopy limit of the
pushforward of its positive ideal-power quotient tensor tower. -/
theorem pushforward_isHomotopyLimit_completionQuotientTower
    (K : RingedSiteDerived JD (constantRingSheaf JD Λ))
    (hK : IsDerivedCompleteWithRespectTo.{u, u, u, u} K (constantIdealSheaf JD I)) :
    HomotopyLimit.IsOf
      (completionQuotientTower (constantIdealSheaf JD I) K ⋙
        modulePushforwardDerived (ofConstantRingSheaf f Λ))
      ((modulePushforwardDerived (ofConstantRingSheaf f Λ)).obj K) := sorry

/-- Completed pullback of a derived-complete object is a homotopy limit of the derived
pullback of its positive ideal-power quotient tensor tower. -/
theorem completedPullback_isHomotopyLimit_completionQuotientTower
    (M : (derivedCompleteObjectProperty.{u, u, u, u}
      (constantIdealSheaf JC I)).FullSubcategory) :
    HomotopyLimit.IsOf
      (completionQuotientTower (constantIdealSheaf JC I) M.obj ⋙
        modulePullbackDerived (ofConstantRingSheaf f Λ))
      ((completedPullback f I).obj M).obj := sorry

end RingedSite.ToposHom.DerivedComplete
