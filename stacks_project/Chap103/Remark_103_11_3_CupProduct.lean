/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage.Tensor
public import stacks_project.Chap103.Proposition_103_11_1_DirectImage
public import stacks_project.Chap103.Remark_103_10_6_Tensor

/-! # Compatibility checks for the direct-image tensor comparison

The comparison retains its explicit adjunction parameter for existing consumers.
The prerequisite source modules remain exported by this compatibility entry.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

#check (AlgebraicGeometry.GroupoidsOver.QCoh.directImage_tensorComparison :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f],
    (QCoh.toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y) → ∀ (F G : QCoh X),
    QCoh.Fppf.tensor ((QCoh.directImage f).obj F) ((QCoh.directImage f).obj G) ⟶
      (QCoh.directImage f).obj (QCoh.Fppf.tensor F G))

#check (CategoryTheory.MonoidalCategory.tensorHom :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {F F' G G' : QCoh X}, (F ⟶ F') → (G ⟶ G') → (F ⊗ G ⟶ F' ⊗ G'))
