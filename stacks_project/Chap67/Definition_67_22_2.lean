/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Remark_67_22_3_EtaleLocal
import StacksCheckRecall

@[expose] public section

/- Definition 67.22.2: let `S` be a scheme. Let `P` be a property of morphisms of
schemes which is étale local on the source-and-target. A morphism `f : X ⟶ Y` of
algebraic spaces over `S` has property `P` if the equivalent conditions of
Lemma 67.22.1 hold. -/
@[stacks 04RD] #check AlgebraicGeometry.AlgebraicSpace.etaleLocal
