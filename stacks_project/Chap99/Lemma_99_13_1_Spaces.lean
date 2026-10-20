/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Fibered.StronglyCartesianSubcategory
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap95.«95_7_0_1_Spaces»
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper

/-!
# Finite-type and fp-flat-proper groupoids of algebraic spaces

The primed categories `Spaces'_ft` and `Spaces'_{fp, flat, proper}` of algebraic
spaces over schemes over a base, with morphisms the cartesian squares.
-/

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.pFtGroupoids :
  ∀ S : AlgebraicGeometry.Scheme.{u},
    AlgebraicGeometry.AlgebraicSpace.Spaces.FtGroupoids S ⥤ CategoryTheory.Over S)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.pFpFlatProperGroupoids :
  ∀ S : AlgebraicGeometry.Scheme.{u},
    AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids S ⥤ CategoryTheory.Over S)
