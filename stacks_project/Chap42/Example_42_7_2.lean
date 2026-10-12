/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import stacks_project.Chap29.Lemma_29_17_5
import stacks_project.Chap42.Situation_42_7_1
import ReasLib.Topology.Specialization.Dimension

open AlgebraicGeometry

universe u

section

variable (k : Type u) [Field k]

/- Supporting fact: the spectrum of a field has a unique point. -/
#check
  (inferInstance : Unique (Spec (CommRingCat.of k)))

/- Example 42.7.2 (1): the spectrum of a field is universally catenary. -/
@[stacks 02QM] #check
  (AlgebraicGeometry.instUniversallyCatenarySpec :
    UniversallyCatenary (Spec (CommRingCat.of k)))

/- Example 42.7.2 (2): the constant-zero function on the spectrum is a dimension function. -/
@[stacks 02QM] #check
  (instIsDimensionFunctionZero :
    IsDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ)))

end
