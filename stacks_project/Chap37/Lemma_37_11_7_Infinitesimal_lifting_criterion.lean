/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Comparison
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.11.7 (Infinitesimal lifting criterion): A scheme morphism is smooth if and
only if it is locally of finite presentation and formally smooth. -/
@[stacks 02H6] #check
  (AlgebraicGeometry.Smooth.iff_locallyOfFinitePresentation_and_formallySmooth :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Smooth f ↔
        AlgebraicGeometry.LocallyOfFinitePresentation f ∧ AlgebraicGeometry.FormallySmooth f)
