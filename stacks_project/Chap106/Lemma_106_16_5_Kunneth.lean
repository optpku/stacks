/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage.Kunneth
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap103.Proposition_103_11_1
public import stacks_project.Chap103.Remark_103_11_3_CupProduct
public import stacks_project.Chap96.Proposition_96_14_3_Comparison

/-! Compatibility checks for the quasi-coherent Künneth construction. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory
universe u

#check (AlgebraicGeometry.GroupoidsOver.QCoh.kunnethMap : ∀ {S : Scheme.{u}}
  {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
  (a : Y ⟶ X) (b : Z ⟶ X)
  [AlgebraicStack.QuasiCompact a] [AlgebraicStack.QuasiSeparated a]
  [AlgebraicStack.QuasiCompact b] [AlgebraicStack.QuasiSeparated b]
  [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)]
  [AlgebraicStack.QuasiCompact (AlgebraicGeometry.GroupoidsOver.QCoh.fibreProductHom a b)]
  [AlgebraicStack.QuasiSeparated (AlgebraicGeometry.GroupoidsOver.QCoh.fibreProductHom a b)],
  QCoh.Fppf.tensor ((QCoh.directImage a).obj (QCoh.structureSheaf Y))
      ((QCoh.directImage b).obj (QCoh.structureSheaf Z)) ⟶
    (QCoh.directImage (AlgebraicGeometry.GroupoidsOver.QCoh.fibreProductHom a b)).obj
      (QCoh.structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)))
