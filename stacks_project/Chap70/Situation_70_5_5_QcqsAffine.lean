/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffine
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine

/-!
# Directed qcqs affine-transition limits of algebraic spaces

The shared owner supplies the limit cone and distinguished-index interface.
The historical imports remain available to existing source consumers.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
variable (c : Cone D) (hc : IsLimit c) (i0 : I)

#check (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.ofCone D c hc i0 :
  AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit D)
