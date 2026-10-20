/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.BaseChange

/-!
# Groupoid-scheme base-change compatibility

This module preserves the former import path for the reusable base-change construction.
-/

open CategoryTheory

universe u

#check (AlgebraicGeometry.GroupoidScheme.baseChange :
  {S S' : AlgebraicGeometry.Scheme.{u}} → (S' ⟶ S) →
    AlgebraicGeometry.GroupoidScheme S → AlgebraicGeometry.GroupoidScheme S')

#check (AlgebraicGeometry.GroupoidScheme.baseChangeProjection :
  {S S' : AlgebraicGeometry.Scheme.{u}} → (f : S' ⟶ S) →
    (G : AlgebraicGeometry.GroupoidScheme S) →
      AlgebraicGeometry.GroupoidScheme.Hom
        (AlgebraicGeometry.GroupoidScheme.changeBase f
          (AlgebraicGeometry.GroupoidScheme.baseChange f G)) G)
