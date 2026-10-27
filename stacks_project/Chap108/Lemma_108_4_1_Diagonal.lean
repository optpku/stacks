/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap110.Lemma_110_53_1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Diagonal

/-!
# Relative diagonals of lifted groupoid fibrations

Typed compatibility checks for the shared mathematical API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.diagonal :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y),
    X ⟶ CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} F F)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.diagonal.comparisonIso :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y),
    ((CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F).toPseudoCone.comparison X).obj
      (Hom.diagonal F) ≅ (PseudoPullbackCone.diagonal F).toPseudoCone.π)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.diagonal.fstIso :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y),
    Hom.diagonal F ≫
      CategoryTheory.TwoFibreProduct.fst.{u + 1, u, u + 1, u + 1} F F ≅ 𝟙 X)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.diagonal.sndIso :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y),
    Hom.diagonal F ≫
      CategoryTheory.TwoFibreProduct.snd.{u + 1, u, u + 1, u + 1} F F ≅ 𝟙 X)

end AlgebraicGeometry.AlgebraicSpace.CohStack
