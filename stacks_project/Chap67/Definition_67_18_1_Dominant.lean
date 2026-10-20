/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-! Compatibility facade for the canonical public owner. -/

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Dominant :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X Y : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ Y) → Prop)
