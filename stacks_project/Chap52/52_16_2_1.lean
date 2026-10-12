/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable (U : Scheme.{u}) [IsNoetherian U] (I : U.IdealSheafData)

/- 52.16.2.1: the completion functor
`Coh(𝒪_U) ⟶ Coh(U, I𝒪_U)`,
`ℱ ↦ ℱ̂`.
-/
@[stacks 0EIK] #check (AlgebraicGeometry.Scheme.CoherentCompletion.functor I :
  RingedSpace.Coh U.toRingedSpace ⥤ Scheme.CoherentFormalModules U I)
