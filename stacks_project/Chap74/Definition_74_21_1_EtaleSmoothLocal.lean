/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal

@[expose] public section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget :
    {S : AlgebraicGeometry.Scheme.{u}} →
      CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S) → Prop)
