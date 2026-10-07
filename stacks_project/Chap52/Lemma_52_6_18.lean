module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Completion
public import stacks_project.Chap52.Lemma_52_6_7
import StacksCheckRecall

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


/- Lemma 52.6.18 (1): derived pushforward preserves derived completeness. -/
@[stacks 099K]
#check (RingedSite.ToposHom.DerivedComplete.pushforwardPreserves
  (C := C) (D := D) (JC := JC) (JD := JD) (O := O) (O' := O') :
  ∀ (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [f.HasModulePushforwardDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I')
    [(I : ringedSiteModuleCategory JC O).IsFiniteType]
    [(I' : ringedSiteModuleCategory JD O').IsFiniteType],
    derivedCompleteObjectProperty.{uD, vD, w, w} I' ≤
      (derivedCompleteObjectProperty.{uC, vC, w, w} I).inverseImage
        (modulePushforwardDerived f))

/- Lemma 52.6.18 (2): derived pullback followed by completion is the left adjoint; no external reflector is required. -/
@[stacks 099K]
#check (RingedSite.ToposHom.DerivedComplete.completedAdjunction
  (C := C) (D := D) (JC := JC) (JD := JD) (O := O) (O' := O') :
  ∀ (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [(SheafOfModules.restrictScalars f.structureMap).IsRightAdjoint]
    [f.HasModulePushforwardDerived] [f.HasModulePullbackDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I')
    [(I : ringedSiteModuleCategory JC O).IsFiniteType]
    [(I' : ringedSiteModuleCategory JD O').IsFiniteType],
    Nonempty (pullbackOfFiniteType f I I' ⊣ pushforward f I I' hI))

end RingedSite.ToposHom.DerivedComplete
