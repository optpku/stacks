module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Descent of universal injectivity for morphisms of algebraic stacks

Universal injectivity descends along surjective, flat, locally of finite
presentation morphisms from algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversallyInjective

/-- A morphism of algebraic stacks is universally injective if its base
change along a surjective, flat, locally of finite presentation morphism from
an algebraic space is universally injective. -/
@[stacks 0DTP]
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [UniversallyInjective (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    UniversallyInjective f :=
  sorry

/-- Universal injectivity of a morphism of algebraic stacks follows from
universal injectivity of the second projection of a bilimit
`PseudoPullbackCone` against a surjective, flat, locally of finite
presentation morphism from an algebraic space. -/
theorem of_isBilimit_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [UniversallyInjective c.snd] :
    UniversallyInjective f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.UniversallyInjective
