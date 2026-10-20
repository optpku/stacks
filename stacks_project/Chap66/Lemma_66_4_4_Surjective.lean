/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Surjectivity of morphisms from schemes to algebraic spaces

A morphism from a scheme to an algebraic space is surjective in the sense of
Spaces, Definition 65.5.1 if and only if the induced map of points is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.ofOver_presheaf_surjective_iff :
  ∀ {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S} (f : ofOver T ⟶ X),
    (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f ↔
      Function.Surjective (Points.map f))
