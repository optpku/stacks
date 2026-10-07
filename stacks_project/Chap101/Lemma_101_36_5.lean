module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Lemma_101_36_4_Unramified

/-!
# Immersions of algebraic stacks are unramified
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom (Immersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.36.5: An immersion of algebraic stacks is unramified. -/
@[stacks 0CIX]
instance unramified_of_immersion {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Immersion f] :
    Unramified f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
