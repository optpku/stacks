/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap92.Lemma_92_25_1_Fibered
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.CotangentSite

universe u

/- Lemma 92.25.1: in the situation above the category `Obj Λ X` is fibred over
`X.smallZariskiSite` via the forgetful functor `forgetZariski`. -/
@[stacks 08V9] #check (AlgebraicGeometry.Scheme.CotangentSite.forgetZariski_isFibered :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec Λ)],
    (AlgebraicGeometry.Scheme.CotangentSite.forgetZariski Λ X).IsFibered)
