module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified

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

/-- The relative diagonal of an unramified morphism of algebraic spaces is an
open immersion. -/
instance isOpenImmersion_diagonal (f : X ⟶ Y) [Unramified f] :
    IsOpenImmersion (pullback.diagonal f) :=
  sorry

/-- A locally of finite type morphism of algebraic spaces whose relative
diagonal is an open immersion is unramified. -/
@[instance 900]
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
