/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Testing representable morphisms of algebraic stacks after fppf base change

A property of morphisms of algebraic spaces that is fppf local on the target
and stable under arbitrary base change may be tested on the base change of a
morphism of algebraic stacks representable by algebraic spaces along a
surjective, flat, locally of finite presentation morphism of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.27.9: Let `P` be a property of morphisms of algebraic spaces which
is fppf local on the target and preserved by arbitrary base change. Let
`f : X ⟶ Y` be a morphism of algebraic stacks representable by algebraic
spaces. Let `g : Z ⟶ Y` be a morphism of algebraic stacks which is surjective,
flat, and locally of finite presentation. Set `W = Z ×_Y X`. Then `f` has `P`
if and only if the projection `W ⟶ Z` has `P`.

The meaning of “has P” is Properties of Stacks, Section 100.3, encoded as
`Groupoids.Hom.has`. Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean
projection is `TwoFibreProduct.snd f g`. -/
@[stacks 0CPP]
theorem has_iff_of_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Groupoids.Hom.has P f ↔
      Groupoids.Hom.has P (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- If the projection `TwoFibreProduct.snd f g` has `P` after base change along a
surjective, flat, locally of finite presentation morphism of algebraic stacks,
then `f` has `P`. -/
theorem has_of_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Groupoids.Hom.has P (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) →
      Groupoids.Hom.has P f :=
  sorry

/-- If `f` has `P`, then the projection `TwoFibreProduct.snd f g` has `P` after
base change along a surjective, flat, locally of finite presentation morphism
of algebraic stacks. -/
theorem has_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Groupoids.Hom.has P f →
      Groupoids.Hom.has P (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces has `P` if
and only if the second projection of a bilimit `PseudoPullbackCone` against a
surjective, flat, locally of finite presentation morphism of algebraic stacks
has `P`. -/
theorem has_iff_of_isBilimit_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f) {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Groupoids.Hom.has P f ↔ Groupoids.Hom.has P c.snd :=
  sorry

end AlgebraicGeometry.AlgebraicStack
