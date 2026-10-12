/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Internal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom

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

/-- The inverse-image structure map of a ringed-topos morphism carries an ideal sheaf into a
specified source ideal when the induced map on underlying sheaves factors through that ideal. -/
def mapsIdeal
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O')) : Prop :=
  ∃ g :
      (inverseImage f.toTopos).obj
          (ToInternal.carrier.{uC, vC, w} (ofCommRingSheaf JC O).structureSheaf
            (I : SheafOfModules (ofCommRingSheaf JC O).structureSheaf)) ⟶
        ToInternal.carrier.{uD, vD, w} (ofCommRingSheaf JD O').structureSheaf
          (I' : SheafOfModules (ofCommRingSheaf JD O').structureSheaf),
    g ≫ ToInternal.carrierMap.{uD, vD, w}
        (ofCommRingSheaf JD O').structureSheaf I'.arrow =
        (inverseImage f.toTopos).map
            (ToInternal.carrierMap.{uC, vC, w}
              (ofCommRingSheaf JC O).structureSheaf I.arrow) ≫
          f.underlyingMap

/-- The factorization characterization of `mapsIdeal`. -/
theorem mapsIdeal_iff
    (f : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JC O))
    (I : Subobject (unitModule JC O)) (I' : Subobject (unitModule JD O')) :
    mapsIdeal f I I' ↔
      ∃ g :
          (inverseImage f.toTopos).obj
              (ToInternal.carrier.{uC, vC, w} (ofCommRingSheaf JC O).structureSheaf
                (I : SheafOfModules (ofCommRingSheaf JC O).structureSheaf)) ⟶
            ToInternal.carrier.{uD, vD, w} (ofCommRingSheaf JD O').structureSheaf
              (I' : SheafOfModules (ofCommRingSheaf JD O').structureSheaf),
        g ≫ ToInternal.carrierMap.{uD, vD, w}
            (ofCommRingSheaf JD O').structureSheaf I'.arrow =
            (inverseImage f.toTopos).map
                (ToInternal.carrierMap.{uC, vC, w}
                  (ofCommRingSheaf JC O).structureSheaf I.arrow) ≫
              f.underlyingMap := sorry

end RingedSite.ToposHom
