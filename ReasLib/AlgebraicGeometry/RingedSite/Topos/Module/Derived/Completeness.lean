/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completeness
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Ideal
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
import Mathlib.Tactic.CrossRefAttribute

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

/-- For a morphism `f` of ringed topoi such that `f^sharp` sends the inverse image
of `I` into `I'`, the derived pushforward `Rf_*` sends objects derived complete with respect to
`I'` into objects derived complete with respect to `I`. -/
@[stacks 099J]
theorem mapsToDerivedComplete
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [f.HasModulePushforwardDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I') :
    derivedCompleteObjectProperty.{uD, vD, w, w} I' ≤
      (derivedCompleteObjectProperty.{uC, vC, w, w} I).inverseImage
        (RingedSite.ToposHom.modulePushforwardDerived f) := sorry

/-- The objectwise form of `mapsToDerivedComplete`: derived pushforward carries every
`I'`-derived-complete object to an `I`-derived-complete object. -/
theorem obj_isDerivedComplete
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    [f.HasModulePushforwardDerived]
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O'))
    (hI : mapsIdeal.{uC, vC, uD, vD, w} f I I')
    (K : ModuleDerived.{w} (ofCommRingSheaf JD O'))
    (hK : IsDerivedCompleteWithRespectTo.{uD, vD, w, w} K I') :
    IsDerivedCompleteWithRespectTo.{uC, vC, w, w}
      ((RingedSite.ToposHom.modulePushforwardDerived f).obj K) I := sorry

end RingedSite.ToposHom.modulePushforwardDerived
