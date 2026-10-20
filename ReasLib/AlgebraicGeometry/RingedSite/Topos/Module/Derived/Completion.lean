/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Completeness
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completion
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.Reflector
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open ObjectProperty.FullSubcategory
open RingedSite
open RingedSite.ToposHom
open SheafOfModules.RingedSite
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe uC vC uD vD w

namespace RingedSite.ToposHom.DerivedComplete

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf JC CommRingCat.{w}} {O' : Sheaf JD CommRingCat.{w}}
variable [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}]
variable [∀ X : C, HasWeakSheafify (JC.over X) AddCommGrpCat.{w}]
variable [∀ X : C, (JC.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ X : D, HasWeakSheafify (JD.over X) AddCommGrpCat.{w}]
variable [∀ X : D, (JD.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The restriction of derived pushforward to the full subcategories of derived-complete
objects. -/
def pushforward
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [f.HasModulePushforwardDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I') :
    (derivedCompleteObjectProperty.{uD, vD, w, w} I').FullSubcategory ⥤
      (derivedCompleteObjectProperty.{uC, vC, w, w} I).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict (modulePushforwardDerived f)
    (modulePushforwardDerived.mapsToDerivedComplete f I I' hI)

/-- Forgetting the restricted pushforward recovers ambient derived pushforward after the
source inclusion. -/
def pushforwardCompInclusionIso
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [f.HasModulePushforwardDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I') :
    pushforward f I I' hI ⋙
        (derivedCompleteObjectProperty.{uC, vC, w, w} I).ι ≅
      (derivedCompleteObjectProperty.{uD, vD, w, w} I').ι ⋙
        modulePushforwardDerived f :=
  restrict.compιIso (modulePushforwardDerived f)
    (modulePushforwardDerived.mapsToDerivedComplete f I I' hI)

/-- Derived pullback on complete objects, followed by an explicit reflector onto the target
derived-complete subcategory. -/
def pullback
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [(SheafOfModules.restrictScalars f.structureMap).IsRightAdjoint]
    [f.HasModulePullbackDerived]
    (I : Subobject (unitModule JC O))
    {I' : Subobject (unitModule JD O')}
    (R : ObjectProperty.Reflector
      (derivedCompleteObjectProperty.{uD, vD, w, w} I')) :
    (derivedCompleteObjectProperty.{uC, vC, w, w} I).FullSubcategory ⥤
      (derivedCompleteObjectProperty.{uD, vD, w, w} I').FullSubcategory :=
  (derivedCompleteObjectProperty.{uC, vC, w, w} I).ι ⋙
    modulePullbackDerived f ⋙ R.toFullSubcategory

/-- Forgetting the completed pullback identifies it with derived pullback followed by the
ambient reflection endofunctor. -/
def pullbackCompInclusionIso
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [(SheafOfModules.restrictScalars f.structureMap).IsRightAdjoint]
    [f.HasModulePullbackDerived]
    (I : Subobject (unitModule JC O))
    {I' : Subobject (unitModule JD O')}
    (R : ObjectProperty.Reflector
      (derivedCompleteObjectProperty.{uD, vD, w, w} I')) :
    pullback f I R ⋙
        (derivedCompleteObjectProperty.{uD, vD, w, w} I').ι ≅
      (derivedCompleteObjectProperty.{uC, vC, w, w} I).ι ⋙
        modulePullbackDerived f ⋙ R.reflection :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _)

/-- The completed pullback is independent, up to canonical natural isomorphism, of the chosen
reflector onto the target derived-complete subcategory. -/
def pullbackIso
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [(SheafOfModules.restrictScalars f.structureMap).IsRightAdjoint]
    [f.HasModulePullbackDerived]
    (I : Subobject (unitModule JC O))
    {I' : Subobject (unitModule JD O')}
    (R S : ObjectProperty.Reflector
      (derivedCompleteObjectProperty.{uD, vD, w, w} I')) :
    pullback f I R ≅ pullback f I S :=
  Functor.isoWhiskerLeft
    (derivedCompleteObjectProperty.{uC, vC, w, w} I).ι
    (Functor.isoWhiskerLeft (modulePullbackDerived f)
      (R.adjunction.leftAdjointUniq S.adjunction))

/-- For compatible finite-type ideals under a morphism of ringed topoi,
derived pushforward preserves derived-complete objects. -/
@[stacks 099K]
theorem pushforwardPreserves
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [f.HasModulePushforwardDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I')
    [(I : ringedSiteModuleCategory JC O).IsFiniteType]
    [(I' : ringedSiteModuleCategory JD O').IsFiniteType] :
    derivedCompleteObjectProperty.{uD, vD, w, w} I' ≤
      (derivedCompleteObjectProperty.{uC, vC, w, w} I).inverseImage
        (modulePushforwardDerived f) :=
  modulePushforwardDerived.mapsToDerivedComplete f I I' hI

/-- For any supplied reflector onto the `I'`-derived-complete objects, derived
pullback followed by reflection is left adjoint to restricted derived pushforward. -/
theorem adjunction
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [(SheafOfModules.restrictScalars f.structureMap).IsRightAdjoint]
    [f.HasModulePushforwardDerived] [f.HasModulePullbackDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I')
    [(I : ringedSiteModuleCategory JC O).IsFiniteType]
    [(I' : ringedSiteModuleCategory JD O').IsFiniteType]
    (R : ObjectProperty.Reflector
      (derivedCompleteObjectProperty.{uD, vD, w, w} I')) :
    Nonempty (pullback f I R ⊣ pushforward f I I' hI) := sorry

/-- The completed pullback uses derived completion supplied by the finite-type
ideal theorem; the caller need not provide a reflector. -/
def pullbackOfFiniteType
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [(SheafOfModules.restrictScalars f.structureMap).IsRightAdjoint]
    [f.HasModulePullbackDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    [(I' : ringedSiteModuleCategory JD O').IsFiniteType] :=
  pullback f I (Completion.reflector I')

/-- The completed pullback is ambient derived pullback followed by completion. -/
def pullbackOfFiniteTypeCompInclusionIso
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [(SheafOfModules.restrictScalars f.structureMap).IsRightAdjoint]
    [f.HasModulePullbackDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    [(I' : ringedSiteModuleCategory JD O').IsFiniteType] :
    pullbackOfFiniteType f I I' ⋙ (derivedCompleteObjectProperty.{uD, vD, w, w} I').ι ≅
      (derivedCompleteObjectProperty.{uC, vC, w, w} I).ι ⋙
        modulePullbackDerived f ⋙ (Completion.reflector I').reflection :=
  pullbackCompInclusionIso f I (Completion.reflector I')

/-- Completed pullback agrees canonically with any other choice of completion. -/
def pullbackOfFiniteTypeIso
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [(SheafOfModules.restrictScalars f.structureMap).IsRightAdjoint]
    [f.HasModulePullbackDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    [(I' : ringedSiteModuleCategory JD O').IsFiniteType]
    (R : ObjectProperty.Reflector (derivedCompleteObjectProperty.{uD, vD, w, w} I')) :
    pullbackOfFiniteType f I I' ≅ pullback f I R :=
  pullbackIso f I (Completion.reflector I') R

/-- For compatible finite-type ideals under a morphism of ringed topoi,
derived pullback followed by derived completion is left adjoint to restricted
derived pushforward. -/
@[stacks 099K]
theorem completedAdjunction
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [(SheafOfModules.restrictScalars f.structureMap).IsRightAdjoint]
    [f.HasModulePushforwardDerived] [f.HasModulePullbackDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I')
    [(I : ringedSiteModuleCategory JC O).IsFiniteType]
    [(I' : ringedSiteModuleCategory JD O').IsFiniteType] :
    Nonempty (pullbackOfFiniteType f I I' ⊣ pushforward f I I' hI) :=
  adjunction f I I' hI (Completion.reflector I')

end RingedSite.ToposHom.DerivedComplete
