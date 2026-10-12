/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Point
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry

/- Exercise 111.33.1 -/
@[stacks 028P] #check
  (AlgebraicGeometry.LocallyRingedSpace.exists_onePoint_not_scheme :
    ∃ X : AlgebraicGeometry.LocallyRingedSpace.{0},
      Nonempty X ∧ Subsingleton X ∧
        ¬ AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.essImage X)
