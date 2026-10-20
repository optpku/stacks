/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Ph

/-!
# Ph covering families of algebraic spaces

The shared algebraic-space ph-covering API is re-exported with the existing
chapter import surface.
-/

@[expose] public section

open CategoryTheory

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.PhCovering :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    {X : AlgebraicGeometry.AlgebraicSpace S}
    (Xi : ι → AlgebraicGeometry.AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X), Prop)
