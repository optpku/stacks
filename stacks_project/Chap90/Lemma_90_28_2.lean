/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalHomotopy
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.28.2: in the category CompleteLocalAlgCat Λ k, if f₁, f₂ : R ⟶ S are
formally homotopic and g : S ⟶ S' is a morphism, then f₁ ≫ g and f₂ ≫ g are
formally homotopic. -/
@[stacks 0DQC] #check (CompleteLocalAlgCat.FormallyHomotopic.compRight :
  ∀ {R S S' : CompleteLocalAlgCat Λ k} {f₁ f₂ : R ⟶ S},
    CompleteLocalAlgCat.FormallyHomotopic f₁ f₂ → (g : S ⟶ S') →
      CompleteLocalAlgCat.FormallyHomotopic (f₁ ≫ g) (f₂ ≫ g))
