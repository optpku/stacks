/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap70.Lemma_70_23_3_BaseChange
public import stacks_project.Chap70.Situation_70_5_5_QcqsAffine

open CategoryTheory Limits
open AlgebraicGeometry AlgebraicSpace

universe u

section

variable {C : Type u} [Category C] {S : Scheme.{u}}
variable (D : C ⥤ AlgebraicSpace S) (c : Cone D) (i₀ : C)
variable {T : AlgebraicSpace S} (t : T ⟶ D.obj i₀)

#check
  (AlgebraicGeometry.AlgebraicSpace.baseChangeOverCone D c i₀ t :
    Cone (AlgebraicGeometry.AlgebraicSpace.baseChangeOverDiagram D i₀ t))

end
