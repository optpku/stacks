module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

/-!
# Immersions of algebraic stacks are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom (Immersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- Lemma 101.17.4. An immersion of algebraic stacks is locally of finite type. -/
@[stacks 06FV]
instance of_immersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Immersion f] :
    LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
