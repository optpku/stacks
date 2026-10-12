/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Dimension along integral morphisms of algebraic spaces

An integral morphism of algebraic spaces cannot increase global dimension, in
the sense of `AlgebraicSpace.dimension`. If the morphism is also surjective,
the dimensions agree.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.15.1 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be an integral
morphism of algebraic spaces over `S`. Then `dimension X ≤ dimension Y`. -/
@[stacks 0EDB]
theorem dimension_le_of_isIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] :
    dimension X ≤ dimension Y :=
  sorry

/-- Lemma 72.15.1 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a surjective
integral morphism of algebraic spaces over `S`. Then `dimension X = dimension Y`. -/
@[stacks 0EDB]
theorem dimension_eq_of_surjective_isIntegralHom {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f] [Surjective f] :
    dimension X = dimension Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
