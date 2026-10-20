/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits Opposite
open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

variable (X : RingedSpace.{u}) (x : X) (U : Opens X)

/- Lemma 17.3.2 (1): the category of sheaves of modules on `X` has all small limits. -/
@[stacks 01AH "(1), limits"]
#check (inferInstance : HasLimits X.Modules)

/- Lemma 17.3.2 (1): forgetting the sheaf condition preserves all small limits. -/
@[stacks 01AH "(1), underlying presheaves"]
#check (inferInstance :
  PreservesLimits (SheafOfModules.forget.{u} X.ringCatSheaf))

/- Lemma 17.3.2 (1): taking sections over `U` preserves all small limits. -/
@[stacks 01AH "(1), sections"]
#check (inferInstance :
  PreservesLimits (SheafOfModules.evaluation X.ringCatSheaf (op U)))

/- Lemma 17.3.2 (2): the category of sheaves of modules on `X` has all small colimits. -/
@[stacks 01AH "(2), colimits"]
#check (inferInstance : HasColimits X.Modules)

/- Lemma 17.3.2 (2): module sheafification preserves all small colimits. -/
@[stacks 01AH "(2), sheafification"]
#check (inferInstance : PreservesColimits X.moduleSheafification)

/- Lemma 17.3.2 (2): taking the stalk at `x` preserves all small colimits. -/
@[stacks 01AH "(2), stalks"]
#check (inferInstance : PreservesColimits (RingedSpace.stalkModuleFunctor x))

/- Lemma 17.3.2 (3): filtered colimits are exact in `X.Modules`. -/
@[stacks 01AH "(3)"]
#check (inferInstance : AB5 X.Modules)

/- Lemma 17.3.2 (4): forgetting the sheaf condition preserves finite direct sums. -/
@[stacks 01AH "(4)"]
#check (inferInstance :
  PreservesFiniteBiproducts (SheafOfModules.forget.{u} X.ringCatSheaf))
