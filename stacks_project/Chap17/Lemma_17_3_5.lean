/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.QuasiCompact.Opens
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits Opposite
open AlgebraicGeometry TopologicalSpace

noncomputable section

universe w u

variable {X : RingedSpace.{u}} {I : Type w}
variable (F : I → X.Modules) [HasCoproduct F]
variable (U : Opens X)
variable [HasCoproduct (fun i ↦ (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (F i))]
variable (hU : IsCompact (U : Set X))

/- Lemma 17.3.5: over a quasi-compact open, the canonical map from the direct sum of sections
to the sections of the direct sum is an isomorphism. -/
@[stacks 01AI]
#check (SheafOfModules.Evaluation.sigmaComparison_isIso_of_quasiCompact
  X.ringCatSheaf (TopologicalSpace.Opens.quasiCompactObject_of_isCompact U hU) F :
    IsIso (sigmaComparison (SheafOfModules.evaluation X.ringCatSheaf (op U)) F))
