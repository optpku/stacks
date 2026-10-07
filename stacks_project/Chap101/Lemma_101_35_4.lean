module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Lemma_101_36_4_Etale

/-!
# Open immersions of algebraic stacks are étale
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom (OpenImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.35.4: An open immersion of algebraic stacks is étale. -/
@[stacks 0CIP]
instance etale_of_openImmersion {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [OpenImmersion f] :
    Etale f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
