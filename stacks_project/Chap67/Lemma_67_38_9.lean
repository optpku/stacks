module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_38_8_Unramified

/-!
# Diagonal criterion for unramified morphisms of algebraic spaces

An unramified morphism of algebraic spaces has open relative diagonal, and a
locally of finite type morphism with open relative diagonal is unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Unramified

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 67.38.9 (1): if `f : X ⟶ Y` is an unramified morphism of algebraic
spaces over a scheme `S`, then the relative diagonal
`pullback.diagonal f : X ⟶ X ×_Y X` is an open immersion. -/
@[stacks 05W1]
instance isOpenImmersion_diagonal (f : X ⟶ Y) [Unramified f] :
    IsOpenImmersion (pullback.diagonal f) :=
  sorry

/-- Lemma 67.38.9 (2): if `f : X ⟶ Y` is a locally of finite type morphism of
algebraic spaces over a scheme `S` and the relative diagonal
`pullback.diagonal f : X ⟶ X ×_Y X` is an open immersion, then `f` is
unramified. -/
@[stacks 05W1, instance 900]
instance of_isOpenImmersion_diagonal (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsOpenImmersion (pullback.diagonal f)] :
    Unramified f :=
  sorry

/-- A morphism of algebraic spaces is unramified if and only if it is locally of
finite type and its relative diagonal is an open immersion. -/
theorem iff_locallyOfFiniteType_and_isOpenImmersion_diagonal (f : X ⟶ Y) :
    Unramified f ↔
      LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f) :=
  sorry

end Unramified

end AlgebraicGeometry.AlgebraicSpace
