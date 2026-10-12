/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Proposition_97_11_5_Space
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace RestrictionOfScalars

universe u

/- Proposition 97.11.5: Let `S` be a scheme. Let `X ⟶ Z ⟶ B` be morphisms of
algebraic spaces over `S`. If `Z ⟶ B` is finite locally free then
`Res_{Z/B}(X)` is an algebraic space. -/
@[stacks 05YF]
#check (instIsAlgebraicSpace :
    ∀ {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)
      [FiniteLocallyFree g],
      IsAlgebraicSpace (smallFunctor f g))
