module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.FiniteType
import StacksCheckRecall

/-!
# Finite morphisms of algebraic spaces versus integral morphisms

A finite morphism of algebraic spaces is integral. An integral morphism of
algebraic spaces which is locally of finite type is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.45.6 (1): A finite morphism of algebraic spaces is integral. -/
@[stacks 0414] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsIntegralHom_of_isFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f],
      IsIntegralHom f)

/- Lemma 67.45.6 (2): An integral morphism of algebraic spaces which is locally of
finite type is finite. -/
@[stacks 0414] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFinite.of_isIntegralHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsIntegralHom f] [LocallyOfFiniteType f], IsFinite f)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsFinite.iff_isIntegralHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f], IsFinite f ↔ IsIntegralHom f)
