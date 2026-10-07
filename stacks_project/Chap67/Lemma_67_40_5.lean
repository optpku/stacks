module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_40_1_Proper

/-!
# Closed immersions of algebraic spaces are proper

A closed immersion of algebraic spaces over a scheme `S` is a proper morphism
of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

/-- Lemma 67.40.5: A closed immersion of algebraic spaces is a proper morphism
of algebraic spaces. -/
@[stacks 04XZ]
instance of_isClosedImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsClosedImmersion f] : Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
