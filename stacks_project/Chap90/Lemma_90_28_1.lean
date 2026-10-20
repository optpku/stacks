/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalHomotopy.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.28.1: being formally homotopic is an equivalence relation on sets
of morphisms in CompleteLocalAlgCat Λ k. -/
@[stacks 0DQB] #check (CompleteLocalAlgCat.FormallyHomotopic.equivalence :
  ∀ {R S : CompleteLocalAlgCat Λ k},
    _root_.Equivalence (CompleteLocalAlgCat.FormallyHomotopic :
      (R ⟶ S) → (R ⟶ S) → Prop))
