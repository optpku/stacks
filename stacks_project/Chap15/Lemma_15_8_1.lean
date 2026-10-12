/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Operations
import StacksCheckRecall

/-!
# Lemma 15.8.1

@stack 07Z7
-/

@[expose] public section

/-!
# Determinantal Ideals

This chapter entry re-exports the neutral matrix-minor API.
-/

/- The determinantal ideal and its generator membership are the setup for Lemma 15.8.1. -/
#check @Matrix.minorIdeal
#check @Matrix.det_submatrix_mem_minorIdeal
#check @Matrix.det_submatrix_mem_minorIdeal_of_rowMap

/- Lemma 15.8.1 (1): fixed-size minor ideals are antitone in the size. -/
@[stacks 07Z7 "(1), antitonicity of minor ideals"]
#check @Matrix.minorIdeal_antitone

/- Lemma 15.8.1 (2): deleting final rows gives the shifted minor-ideal containment. -/
@[stacks 07Z7 "(2), initial-row minor bound"]
#check @Matrix.minorIdeal_initialRows_le

/- Lemma 15.8.1 (3): left multiplication does not enlarge a minor ideal. -/
@[stacks 07Z7 "(3), left multiplication of minor ideals"]
#check @Matrix.minorIdeal_mul_left_le

/- Lemma 15.8.1 (4): block-diagonal minor ideals satisfy the antidiagonal product formula. -/
@[stacks 07Z7 "(4), block-diagonal minor formula"]
#check @Matrix.minorIdeal_fromBlocks
