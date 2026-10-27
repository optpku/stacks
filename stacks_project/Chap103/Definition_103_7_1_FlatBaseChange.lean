/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.«96_9_4_1_Comparison»

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.FlatBaseChange

@[expose] public section

universe u

#check (AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X],
    AlgebraicGeometry.GroupoidsOver.etaleModules X → Prop)
