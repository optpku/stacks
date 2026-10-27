/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.QCoh.AffineTensor
public import stacks_project.Chap96.Lemma_96_15_1_Tensor

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Limits FiberedCategoryOver.Groupoids
open scoped Bicategory TensorProduct

universe u

/-! Compatibility checks for evaluated pushforward modules and their raw unit operation. -/

#check (AlgebraicGeometry.GroupoidsOver.QCoh.algebraModule :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {B : Type u} [CommRing B] (F : QCoh X ⥤ ModuleCat.{u} B)
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g], ModuleCat.{u} B)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.algebraOne :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {B : Type u} [CommRing B] (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_unit : F.obj (AlgebraicGeometry.GroupoidsOver.QCoh.structureSheaf X) ≅ ModuleCat.of B B)
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g],
    AlgebraicGeometry.GroupoidsOver.QCoh.algebraModule F g)
