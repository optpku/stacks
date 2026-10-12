/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Remark_87_35_2
import StacksCheckRecall

/-!
# Affine formal algebraic spaces whose regular functions do not separate points
-/

@[expose] public section

open AlgebraicGeometry

/- Lemma 110.75.2: there exists an affine formal algebraic space whose regular
functions do not separate points: some directed affine thickening presentation as
in Definition 87.9.1 has inverse-limit global sections a field, while the reduced
space has infinitely many points. -/
@[stacks 0CBD] #check exists_isAffineFormalAlgebraicSpace_regularFunctions_not_separatePoints
