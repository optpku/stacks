/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Jacobson.Cardinality
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.35.12

@stack 046V

The residue fields of a sufficiently large scalar extension are algebraic, and the scalar extension
is Jacobson.
-/

/- Lemma 10.35.12 (1): algebraicity of maximal-ideal residue fields after scalar extension. -/
@[stacks 046V "(1), algebraic residue fields"]
#check @Algebra.IsAlgebraic.residueField_tensorProduct_of_cardinalMk_lt

/- Lemma 10.35.12 (2): the Jacobson-ring conclusion after scalar extension. -/
@[stacks 046V "(2), Jacobson scalar extension"]
#check @IsJacobsonRing.tensorProduct_of_cardinalMk_lt
