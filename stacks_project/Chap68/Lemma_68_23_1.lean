module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Lemma_68_23_1_Jacobson

/-!
# Locally of finite type over Jacobson algebraic spaces

A morphism of algebraic spaces that is locally of finite type into a Jacobson
target has Jacobson source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFiniteType

/-- Lemma 68.23.1: Let `S` be a scheme. Let `X` be a Jacobson algebraic space over `S`.
Any algebraic space locally of finite type over `X` is Jacobson. -/
@[stacks 0BA3]
theorem isJacobson {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsJacobson Y] : IsJacobson X :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
