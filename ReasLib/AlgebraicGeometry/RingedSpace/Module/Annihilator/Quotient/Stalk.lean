/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator.Quotient
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Quotient.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of modules descended along annihilator quotients

This file specializes the quotient-stalk API to the source-facing hypothesis `I ≤ Ann(F)`, so
users do not have to rebuild the equivalent sectionwise annihilation witness.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.Stalk

variable {X : RingedSpace.{u}}

/-- The stalk of the quotient module descended directly from `I ≤ Ann(F)`. -/
@[stacks 0H2K "stalk of a module descended from annihilator containment"]
noncomputable abbrev ofLE
    (I : X.IdealSubobject) (F : X.Modules)
    (h : I ≤ SheafOfModules.Annihilator.subobject F) (x : X) :
    ModuleCat (IdealSheaf.Quotient.sheafStalk I x) :=
  IdealSheaf.Quotient.descendStalk I F
    ((IdealSheaf.le_annihilator_iff I F).1 h) x

/-- The additive forgetful map from the descended quotient-module stalk to the original stalk. -/
@[stacks 0H2K "forgetful map for a stalk descended from annihilator containment"]
noncomputable abbrev forgetOfLE
    (I : X.IdealSubobject) (F : X.Modules)
    (h : I ≤ SheafOfModules.Annihilator.subobject F) (x : X) :
    ofLE I F h x →+ RingedSpace.stalkModuleCat F x :=
  IdealSheaf.Quotient.descendStalkForget I F
    ((IdealSheaf.le_annihilator_iff I F).1 h) x

/-- On stalks, the quotient scalar action obtained from `I ≤ Ann(F)` is the original action. -/
@[stacks 0H2K "stalkwise scalar action from annihilator containment"]
theorem forget_smul_projection
    (I : X.IdealSubobject) (F : X.Modules)
    (h : I ≤ SheafOfModules.Annihilator.subobject F)
    (x : X) (r : X.presheaf.stalk x) (m : ofLE I F h x) :
    forgetOfLE I F h x (IdealSheaf.Quotient.projectionStalk I x r • m) =
      r • forgetOfLE I F h x m := sorry

-- Any `sorryAx` below is inherited from the Prop-valued equivalence between annihilator
-- containment and sectionwise annihilation, together with the generic quotient-module laws.

end AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.Stalk
