/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap75.Lemma_75_10_5_Gamma
public import stacks_project.Chap75.Lemma_75_20_1_ProjectionFormula
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula.Cohomology

/-! # Tensor-pullback and cohomology comparison compatibility -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory ComplexShape

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.complexTensorPullback :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B),
    CochainComplex (Modules X) ℤ)
