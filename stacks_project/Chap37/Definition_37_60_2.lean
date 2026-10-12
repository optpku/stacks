/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap37.Lemma_37_60_1
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 37.60.2: a morphism of schemes is pseudo-coherent when the equivalent
conditions of Lemma 37.60.1 hold. -/
@[stacks 067Z] #check
  (AlgebraicGeometry.PseudoCoherent :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}}, (X ⟶ S) → Prop)
