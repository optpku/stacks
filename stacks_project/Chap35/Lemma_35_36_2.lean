/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty.AffineCriterion
import StacksCheckRecall

open CategoryTheory

universe u

open AlgebraicGeometry

/- Lemma 35.36.2: A scheme morphism property stable under base change and finite
coproducts satisfies descent for a non-Zariski topology if descent data for affine
singleton covers are effective. -/
@[stacks 02W3]
#check (CategoryTheory.MorphismProperty.SatisfiesDescent.of_affine :
  ∀ (P : MorphismProperty Scheme.{u}) (τ : DescentTopology) (_ : τ ≠ .zariski)
    [P.IsStableUnderBaseChange] [P.IsStableUnderFiniteCoproducts],
    (∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
      (p : X ⟶ S) (_ : Presieve.singleton p ∈ τ.precoverage S)
      (D : Scheme.DescentData (fun _ : PUnit ↦ X) (fun _ ↦ p)),
        P (D.obj PUnit.unit).hom → D.IsEffective) →
      P.SatisfiesDescent τ)
