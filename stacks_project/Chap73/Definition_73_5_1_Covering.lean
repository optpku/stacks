/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Smooth
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Smooth covering families of algebraic spaces

A smooth covering of an algebraic space is an indexed family of smooth morphisms
that is jointly surjective on points.
-/

@[expose] public section

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.SmoothCovering :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {ι : Type v}, (ι → CategoryTheory.Over X) → Prop)
