module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral
import StacksCheckRecall

/-!
# Finite morphisms of algebraic spaces versus integral morphisms

A finite morphism of algebraic spaces is integral. An integral morphism of
algebraic spaces which is locally of finite type is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.45.6 (1): A finite morphism of algebraic spaces is integral. -/
@[stacks 0414] #check
  (instIsIntegralHom_of_isFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f],
      IsIntegralHom f)

namespace IsFinite

/-- Lemma 67.45.6 (2): An integral morphism of algebraic spaces which is locally of
finite type is finite. -/
@[stacks 0414]
theorem of_isIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] [LocallyOfFiniteType f] : IsFinite f :=
  sorry

/-- Under a locally-of-finite-type hypothesis, a morphism of algebraic spaces is
finite if and only if it is integral. -/
theorem iff_isIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] : IsFinite f ↔ IsIntegralHom f :=
  sorry

end IsFinite

end AlgebraicGeometry.AlgebraicSpace
