/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_9_Lift
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.4.9: let `S` be a scheme. Let `X`, `Y` be algebraic spaces over `S`. Let
`X' ⊂ X` be an open subspace. Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S`.
Then `f` factors through `X'` if and only if `|f| : |Y| ⟶ |X|` factors through
`|X'| ⊂ |X|`. -/
@[stacks 03IE] #check
  (IsOpenImmersion.exists_lift_iff_range_subset :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ X) [IsOpenImmersion i] (f : Y ⟶ X),
      (∃ g : Y ⟶ Z, g ≫ i = f) ↔
        Set.range (Points.map f) ⊆ Set.range (Points.map i))
