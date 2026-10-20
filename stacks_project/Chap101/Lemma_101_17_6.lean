module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.Descent

/-!
# Descent of locally of finite type morphisms of algebraic stacks along fppf
algebraic-space coverings

Local finite type of a morphism of algebraic stacks follows from local finite
type of its base change along a surjective, flat, locally of finite
presentation morphism from an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/- Lemma 101.17.6: Let `f : X ⟶ Y` be a morphism of algebraic stacks, and let
`g : W.toGroupoids ⟶ Y` be a `Groupoids.Hom.Surjective`, `Groupoids.Hom.Flat`,
and `Groupoids.Hom.LocallyOfFinitePresentation` morphism from an algebraic
space `W`. If the base change `TwoFibreProduct.snd f g` is locally of finite
type, then `f` is locally of finite type.

Stacks writes the base change as `W ×_Y X ⟶ W`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06U7] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.of_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [LocallyOfFiniteType (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)],
    LocallyOfFiniteType f)

/- Local finite type of a morphism of algebraic stacks follows from local
finite type of the second projection of a bilimit `PseudoPullbackCone` against
a surjective, flat, locally of finite presentation morphism from an algebraic
space. -/
#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.of_isBilimit_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [LocallyOfFiniteType c.snd],
    LocallyOfFiniteType f)

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
