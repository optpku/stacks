/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SectionsWithSupport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_31_3_LocallyProjective
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-! Typed compatibility checks for sections supported on a closed subset. -/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

variable {S : Scheme.{u}} {X U : AlgebraicSpace S}
variable (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.sectionsWithSupportFunctor ι :
  X.Modules ⥤ X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.sectionsWithSupportIn ι F : X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.sectionsWithSupportInι ι F :
  sectionsWithSupportIn ι F ⟶ F)

variable [QuasiCompact ι] [F.IsQuasicoherent]

#check (AlgebraicGeometry.AlgebraicSpace.Modules.sectionsWithSupportIn_isQuasicoherent ι F :
  (sectionsWithSupportIn ι F).IsQuasicoherent)
