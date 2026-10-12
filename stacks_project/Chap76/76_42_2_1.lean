/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.«76_42_2_1_Category»
public import stacks_project.Chap76.«76_42_2_1_Completion»
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
@[stacks 08B4] #check
  (CoherentCompletion.functor I : Coh X ⥤ CoherentFormalModules X I)
