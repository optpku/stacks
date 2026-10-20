module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Descent of universal homeomorphisms of algebraic stacks

Universal homeomorphisms descend along surjective, flat, locally of finite
presentation morphisms from algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism

/-- A morphism of algebraic stacks is a universal homeomorphism if the second
projection of a bilimit `PseudoPullbackCone` against a surjective, flat,
locally of finite presentation morphism from an algebraic space is a
universal homeomorphism. -/
theorem of_isBilimit_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [UniversalHomeomorphism c.snd] :
    UniversalHomeomorphism f :=
  sorry

/-- A morphism of algebraic stacks is a universal homeomorphism if its base
change along a surjective, flat, locally of finite presentation morphism from
an algebraic space is a universal homeomorphism. -/
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [UniversalHomeomorphism (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    UniversalHomeomorphism f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism
