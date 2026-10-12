/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Definition_72_11_1_GeometricallyReduced
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.11.1 (1): an algebraic space `X` over a field `k` is geometrically
reduced at a point `x` of `|X|` if the étale local ring `𝒪_{X, x̄}` is geometrically
reduced over `k`. -/
@[stacks 0DMQ] #check
  (GeometricallyReducedAt :
    {k : Type u} → [Field k] → (X : AlgebraicSpace (Spec (of k))) → Points X → Prop)

/- Definition 72.11.1 (2): an algebraic space `X` over a field `k` is geometrically
reduced over `k` if `X` is geometrically reduced at every point of `|X|`. -/
@[stacks 0DMQ] #check
  (GeometricallyReduced :
    {k : Type u} → [Field k] → AlgebraicSpace (Spec (of k)) → Prop)
