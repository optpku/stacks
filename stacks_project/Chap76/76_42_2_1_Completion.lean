/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap76.«76_42_2_1_Category»
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion

/-! Compatibility check for the shared coherent completion functor. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u
variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNoetherian X]
variable (I : IdealSubobject X) [IsQuasiCoherent I]

#check (AlgebraicGeometry.AlgebraicSpace.CoherentCompletion.functor I :
  Coh X ⥤ CoherentFormalModules X I)
