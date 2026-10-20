/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Separation conditions on algebraic spaces

The diagonal and separation conditions are provided by their shared mathematical owner.
The component API for morphisms remains available to existing consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

#check (AlgebraicGeometry.AlgebraicSpace.diag :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    F.functorOfPoints ⟶ F.functorOfPoints ⨯ F.functorOfPoints)
