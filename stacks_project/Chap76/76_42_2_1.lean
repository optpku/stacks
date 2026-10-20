/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNoetherian X]
variable (I : IdealSubobject X) [IsQuasiCoherent I]

/- 76.42.2.1: the completion functor
`Coh(𝒪_X) ⟶ Coh(X, I)`,
`F ↦ completion F`.
-/
@[stacks 08B4] #check (AlgebraicGeometry.AlgebraicSpace.CoherentCompletion.functor I :
  Coh X ⥤ CoherentFormalModules X I)
