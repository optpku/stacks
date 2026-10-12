/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Definition 71.19.1: A morphism `X' ⟶ X` of algebraic spaces over a scheme `S` is a
`U`-admissible blowup if some finitely presented closed immersion `Z ⟶ X` is disjoint
from the open subspace `U ⊂ X` and `X'` is isomorphic to the blowup of `X` in `Z`. -/
@[stacks 086B] #check (IsAdmissibleBlowup :
  {S : Scheme.{u}} → {X X' : AlgebraicSpace S} → OpenSubspace X → (X' ⟶ X) → Prop)

#check (isAdmissibleBlowup_iff :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (U : OpenSubspace X) (f : X' ⟶ X),
    IsAdmissibleBlowup U f ↔
      ∃ Z : ClosedSubspace X,
        IsBlowup f Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet)
