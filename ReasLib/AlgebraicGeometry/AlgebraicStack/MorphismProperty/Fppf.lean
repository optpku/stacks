/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Testing representable morphism properties after fppf base change

A base-change-stable property of algebraic-space morphisms that is fppf local
on the target can be tested after surjective, flat, locally finitely presented
base change of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks representable by algebraic spaces has a
base-change-stable, fppf-target-local property `P` if and only if its canonical
base change along a surjective, flat, locally of finite presentation morphism
has `P`. The base-changed morphism is the second projection of the 2-fibre
product. -/
theorem has_iff_of_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    Groupoids.Hom.has P f ↔
      Groupoids.Hom.has P (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces has a
base-change-stable, fppf-target-local property `P` if and only if the second
projection of an algebraic bilimit cone against a surjective, flat, locally of
finite presentation morphism has `P`. -/
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
