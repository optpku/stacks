/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_13_1
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap99.«99_7_1_1_Functor»

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Functor

/-!
# The Grothendieck Hilbert functor on algebraic spaces

This module constructs the contravariant Hilbert functor of a finite-presentation
morphism of algebraic spaces. A test scheme `T` over `B` is sent to the set of
closed subspaces `Z ⊂ X_T` for which `Z ⟶ T` is of finite presentation, flat,
and proper, identified when they have the same ideal sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f],
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))
