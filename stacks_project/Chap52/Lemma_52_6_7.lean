/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap52.Lemma_52_6_7_IdealMap
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Completeness
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.LeftExactAdjunction
open CategoryTheory.MorphismOfTopoiIn
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalRing
open RingedSite
open SheafOfModules.RingedSite

noncomputable section

universe uC vC uD vD w

open RingedSite.Hom.ModuleDerived
open RingedSite.Hom

open RingedSite.ToposHom

namespace RingedSite.ToposHom.modulePushforwardDerived

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf JC CommRingCat.{w}} {O' : Sheaf JD CommRingCat.{w}}
variable [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}]

/- Lemma 52.6.7: derived pushforward preserves completeness for ideals compatible
with the actual inverse-image structure morphism. -/
@[stacks 099J]
#check (RingedSite.ToposHom.modulePushforwardDerived.mapsToDerivedComplete.{uC, vC, uD, vD, w} :
    ∀ (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [f.HasModulePushforwardDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I'),
    derivedCompleteObjectProperty.{uD, vD, w, w} I' ≤
      (derivedCompleteObjectProperty.{uC, vC, w, w} I).inverseImage
        (RingedSite.ToposHom.modulePushforwardDerived f))

/- Objectwise form of the canonical preservation theorem. -/
#check (RingedSite.ToposHom.modulePushforwardDerived.obj_isDerivedComplete.{uC, vC, uD, vD, w} :
    ∀ (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [f.HasModulePushforwardDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I')
    (K : ModuleDerived.{w} (ofCommRingSheaf JD O'))
    (hK : IsDerivedCompleteWithRespectTo.{uD, vD, w, w} K I'),
    IsDerivedCompleteWithRespectTo.{uC, vC, w, w}
      ((RingedSite.ToposHom.modulePushforwardDerived f).obj K) I)

end RingedSite.ToposHom.modulePushforwardDerived
