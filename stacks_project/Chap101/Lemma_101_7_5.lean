module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Closed immersions of algebraic stacks are quasi-compact

A closed immersion of algebraic stacks is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 101.7.5: A closed immersion of algebraic stacks is quasi-compact. -/
@[stacks 0CL1]
instance ClosedImmersion.quasiCompact {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    AlgebraicStack.QuasiCompact f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
