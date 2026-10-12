/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Ideal


@[expose] public section

open CategoryTheory
open CategoryTheory.LeftExactAdjunction
open CategoryTheory.MorphismOfTopoiIn
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalModule
open RingedSite
open SheafOfModules.RingedSite

noncomputable section

universe uC vC uD vD w

namespace RingedSite.ToposHom

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf JC CommRingCat.{w}} {O' : Sheaf JD CommRingCat.{w}}
variable [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}]

/- Canonical ideal compatibility, re-exported for existing item consumers. -/
#check (RingedSite.ToposHom.mapsIdeal.{uC, vC, uD, vD, w} :
  ∀ (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O)),
    Subobject (unitModule JC O) → Subobject (unitModule JD O') → Prop)

end RingedSite.ToposHom
