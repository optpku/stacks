/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap10.Lemma_10_75_3_Support.Core

@[expose] public section

/-!
The row-cycle proof scaffolding formerly kept here consisted entirely of private, unconsumed
declarations. Downstream support uses the canonical antidiagonal and staircase API from `Core`.
-/

#check @totalAntidiagonalLift_totalToRowCokernelComponent
#check @totalAntidiagonalLift_cycleOfStaircase
#check @extendAntidiagonalFamily
#check @staircaseTransport_comm
