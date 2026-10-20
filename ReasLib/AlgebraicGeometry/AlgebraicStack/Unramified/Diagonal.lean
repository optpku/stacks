module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

/-!
# Diagonal criterion for unramified morphisms of algebraic stacks

A morphism of algebraic stacks is unramified if and only if it is locally of
finite type and its relative 2-diagonal is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- A morphism of algebraic stacks is unramified if and only if it is locally
of finite type and its relative 2-diagonal is étale. -/
theorem iff_locallyOfFiniteType_and_etale_diagonal (f : X ⟶ Y) :
    Unramified f ↔
      LocallyOfFiniteType f ∧ Etale (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- An unramified morphism of algebraic stacks is locally of finite type. -/
instance locallyOfFiniteType (f : X ⟶ Y) [Unramified f] :
    LocallyOfFiniteType f :=
  ((iff_locallyOfFiniteType_and_etale_diagonal f).mp inferInstance).1

/-- The relative 2-diagonal of an unramified morphism of algebraic stacks is
étale. -/
theorem etale_diagonal (f : X ⟶ Y) [Unramified f] :
    Etale (Hom.diagonal.{u + 1, u, u + 1} f) :=
  ((iff_locallyOfFiniteType_and_etale_diagonal f).mp inferInstance).2

/-- A locally of finite type morphism of algebraic stacks whose relative
2-diagonal is étale is unramified. -/
theorem of_etale_diagonal (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Etale (Hom.diagonal.{u + 1, u, u + 1} f)] :
    Unramified f :=
  (iff_locallyOfFiniteType_and_etale_diagonal f).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.AlgebraicStack.Unramified
