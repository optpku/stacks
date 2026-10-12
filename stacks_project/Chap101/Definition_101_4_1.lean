/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_4_1_Separation
import StacksCheckRecall

@[expose] public section

/- Definition 101.4.1 (1): a morphism of algebraic stacks is DM if its
relative 2-diagonal is unramified. -/
@[stacks 04YW] #check AlgebraicGeometry.AlgebraicStack.DM

/- Definition 101.4.1 (2): a morphism of algebraic stacks is quasi-DM if its
relative 2-diagonal is locally quasi-finite. -/
@[stacks 04YW] #check AlgebraicGeometry.AlgebraicStack.QuasiDM

/- Definition 101.4.1 (3): a morphism of algebraic stacks is separated if its
relative 2-diagonal is proper. -/
@[stacks 04YW] #check AlgebraicGeometry.AlgebraicStack.Separated

/- Definition 101.4.1 (4): a morphism of algebraic stacks is quasi-separated if
its relative 2-diagonal is quasi-compact and quasi-separated. -/
@[stacks 04YW] #check AlgebraicGeometry.AlgebraicStack.QuasiSeparated
