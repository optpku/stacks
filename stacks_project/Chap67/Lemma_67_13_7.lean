/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ProjectionFormula.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- Lemma 67.13.7 -/
@[stacks 04G0] #check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.isIso_projectionFormula :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
      (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
      (B : Sheaf (smallEtaleTopology Z) CommRingCat.{u})
      (φ : (etaleRingedSite X A).structureSheaf ⟶
        (ringPushforward i).obj (etaleRingedSite Z B).structureSheaf)
      (F : SheafOfModules.{u} (etaleRingedSite X A).structureSheaf)
      (G : SheafOfModules.{u} (etaleRingedSite Z B).structureSheaf),
      IsIso (projectionFormula i φ F G))
