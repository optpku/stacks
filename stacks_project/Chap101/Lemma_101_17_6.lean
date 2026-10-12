/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

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

/-- Lemma 101.17.6: Let `f : X ⟶ Y` be a morphism of algebraic stacks, and let
`g : W.toGroupoids ⟶ Y` be a `Groupoids.Hom.Surjective`, `Groupoids.Hom.Flat`,
and `Groupoids.Hom.LocallyOfFinitePresentation` morphism from an algebraic
space `W`. If the base change `TwoFibreProduct.snd f g` is locally of finite
type, then `f` is locally of finite type.

Stacks writes the base change as `W ×_Y X ⟶ W`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06U7]
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [LocallyOfFiniteType (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    LocallyOfFiniteType f :=
  sorry

/-- Local finite type of a morphism of algebraic stacks follows from local
finite type of the second projection of a bilimit `PseudoPullbackCone` against
a surjective, flat, locally of finite presentation morphism from an algebraic
space. -/
theorem of_isBilimit_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [LocallyOfFiniteType c.snd] :
    LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
