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
