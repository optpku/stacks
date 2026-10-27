/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.AffineTensorPullback
public import stacks_project.Chap96.Lemma_96_15_1_Tensor

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open scoped Bicategory

universe u

/- Affine tensor pullback of quasi-coherent modules. -/
#check (AlgebraicGeometry.GroupoidsOver.QCoh.tensorPullback :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left],
    (GroupoidsOver.slice U ⟶ X) →
      (GroupoidsOver.QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤)))
