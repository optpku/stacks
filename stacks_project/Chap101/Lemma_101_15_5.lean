module

import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism.Descent
import StacksCheckRecall

/-!
# Descent of universal homeomorphisms of algebraic stacks along fppf
algebraic-space coverings

A morphism of algebraic stacks is a universal homeomorphism if its base change
along a surjective, flat, locally of finite presentation morphism from an
algebraic space is a universal homeomorphism.
-/

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.15.5: Let `f : X ⟶ Y` be a morphism of algebraic stacks, and let
`g : W.toGroupoids ⟶ Y` be a `Groupoids.Hom.Surjective`, `Groupoids.Hom.Flat`,
and `Groupoids.Hom.LocallyOfFinitePresentation` morphism from an algebraic
space `W`. If the base change `TwoFibreProduct.snd f g` is a universal
homeomorphism, then `f` is a universal homeomorphism.

Stacks writes the base change as `W ×_Y X ⟶ W`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 0DTQ] #check
  (AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism.of_covering :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [AlgebraicStack.UniversalHomeomorphism
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)],
    AlgebraicStack.UniversalHomeomorphism f)

/- A morphism of algebraic stacks is a universal homeomorphism if the second
projection of a bilimit `PseudoPullbackCone` against a surjective, flat,
locally of finite presentation morphism from an algebraic space is a
universal homeomorphism. -/
#check
  (AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism.of_isBilimit_covering :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [AlgebraicStack.UniversalHomeomorphism c.snd],
    AlgebraicStack.UniversalHomeomorphism f)
