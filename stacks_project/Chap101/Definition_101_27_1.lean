/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap101.Definition_101_27_1_FinitePresentation
import StacksCheckRecall

@[expose] public section

/- Definition 101.27.1 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
locally of finite presentation if the equivalent conditions of Lemma 101.16.1
hold with `P` = locally of finite presentation. -/
@[stacks 06Q2] #check AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/- Definition 101.27.1 (2): a morphism `f : X ⟶ Y` of algebraic stacks is of
finite presentation if it is locally of finite presentation, quasi-compact, and
quasi-separated. -/
@[stacks 06Q2] #check AlgebraicGeometry.AlgebraicStack.FinitePresentation
