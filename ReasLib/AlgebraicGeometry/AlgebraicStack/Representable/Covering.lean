module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Representability of algebraic-stack morphisms on an fppf covering

A morphism of algebraic stacks is representable by algebraic spaces if and only
if its 2-fibre product with an algebraic-space covering that is surjective,
flat, and locally of finite presentation is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is representable by algebraic spaces if and
only if its 2-fibre product with a surjective, flat, locally finitely presented
morphism from an algebraic space is an algebraic space. -/
@[stacks 04ZP]
theorem relativelyRepresentableByAlgebraicSpaces_iff_of_covering
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g] :
    relativelyRepresentableByAlgebraicSpaces f ↔
      IsRepresentableByAlgebraicSpace
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
