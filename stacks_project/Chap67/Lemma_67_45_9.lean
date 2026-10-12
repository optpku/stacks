/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Finite morphisms of algebraic spaces versus affine proper morphisms

A morphism of algebraic spaces is finite if and only if it is affine and
proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Affine

/-- A finite morphism of algebraic spaces is affine. -/
instance of_isFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsFinite f] : Affine f :=
  sorry

end Affine

namespace Proper

/-- A finite morphism of algebraic spaces is proper. -/
instance of_isFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsFinite f] : Proper f :=
  sorry

end Proper

namespace IsFinite

/-- An affine and proper morphism of algebraic spaces is finite. -/
theorem of_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Affine f] [Proper f] : IsFinite f :=
  sorry

/-- Lemma 67.45.9: A morphism of algebraic spaces is finite if and only if it
is affine and proper. -/
@[stacks 04NZ]
theorem iff_proper_and_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsFinite f ↔ Proper f ∧ Affine f :=
  sorry

/-- The morphism property of being a finite morphism of algebraic spaces
equals the infimum of being proper and affine. -/
theorem eq_proper_inf_affine {S : Scheme.{u}} :
    (@IsFinite S : MorphismProperty (AlgebraicSpace S)) =
      (@Proper S ⊓ @Affine S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end IsFinite

end AlgebraicGeometry.AlgebraicSpace
