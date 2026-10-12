/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.«87_2_0_1_LocallyTopologicallyRingedSpace»
public import stacks_project.Chap87.«87_2_0_1_Spf»
import StacksCheckRecall

@[expose] public section

/-
87.2.0.1 Morphisms in LTRS from (Spf B, O_Spf B) to (Spf A, O_Spf A) are identified
with continuous ring homomorphisms Hom_cont(A, B).
-/
@[stacks 0AHZ]
#check AlgebraicGeometry.Spf.homEquiv
