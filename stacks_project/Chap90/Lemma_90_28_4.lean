/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalHomotopy.MinimalPrime
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/- Lemma 90.28.4: in the category CompleteLocalAlgCat Λ k, if f₁, f₂ : R ⟶ S are
formally homotopic and p ⊂ R is a minimal prime ideal, then f₁(p)S = f₂(p)S as
ideals. -/
@[stacks 0DQE] #check (CompleteLocalAlgCat.FormallyHomotopic.map_minimalPrime :
  ∀ {R S : CompleteLocalAlgCat Λ k} {f₁ f₂ : R ⟶ S},
    CompleteLocalAlgCat.FormallyHomotopic f₁ f₂ → ∀ {p : Ideal R.carrier},
      IsMinimalPrime p → p.map f₁.hom = p.map f₂.hom)

end CompleteLocalAlgCat
