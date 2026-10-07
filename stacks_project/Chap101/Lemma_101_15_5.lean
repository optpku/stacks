module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap101.Definition_101_15_2_UniversalHomeomorphism

/-!
# Descent of universal homeomorphisms of algebraic stacks along fppf
algebraic-space coverings

A morphism of algebraic stacks is a universal homeomorphism if its base change
along a surjective, flat, locally of finite presentation morphism from an
algebraic space is a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism

/-- Lemma 101.15.5: Let `f : X ⟶ Y` be a morphism of algebraic stacks, and let
`g : W.toGroupoids ⟶ Y` be a `Groupoids.Hom.Surjective`, `Groupoids.Hom.Flat`,
and `Groupoids.Hom.LocallyOfFinitePresentation` morphism from an algebraic
space `W`. If the base change `TwoFibreProduct.snd f g` is a universal
homeomorphism, then `f` is a universal homeomorphism.

Stacks writes the base change as `W ×_Y X ⟶ W`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 0DTQ]
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [UniversalHomeomorphism (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    UniversalHomeomorphism f :=
  sorry

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

end AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism
