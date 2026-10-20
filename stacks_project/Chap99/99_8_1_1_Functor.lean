/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap99.«99_7_1_1_Functor»
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

/- The proper-support Quot functor of finitely presented flat quotients. -/
#check (AlgebraicGeometry.AlgebraicSpace.Quot.quot :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent], (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))
