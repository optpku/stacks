/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)

/- 30.23.3.1: the completion functor
`Coh(𝒪_X) ⟶ Coh(X, 𝓘)`,
`ℱ ↦ completion ℱ`.
-/
@[stacks 0880] #check
  (Scheme.CoherentCompletion.functor I :
    RingedSpace.Coh X.toRingedSpace ⥤ Scheme.CoherentFormalModules X I)
