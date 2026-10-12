/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Lemma_106_8_7_Infinitesimal_lifting_criterion_Comparison
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 106.8.7 (Infinitesimal lifting criterion): A morphism of algebraic stacks
is smooth if and only if it is locally of finite presentation and formally
smooth. -/
@[stacks 0DP0] #check
  (Smooth.iff_locallyOfFinitePresentation_and_formallySmooth :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y),
      Smooth f ↔ LocallyOfFinitePresentation f ∧ FormallySmooth f)
