/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Points of a cartesian square of algebraic spaces

A cartesian square of algebraic spaces over a scheme `S` induces a comparison from the
points of the apex to the set-theoretic fibre product of points. That comparison is
surjective, though not in general injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.Points.pullbackComparison_surjective :
  ∀ {S : Scheme.{u}} {P X Y Z : AlgebraicSpace S}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g),
    Function.Surjective (Points.pullbackComparison h : Points P → Points.pullbackObj f g))
