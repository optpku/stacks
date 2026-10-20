/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalHomotopy
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Formally homotopic morphisms of complete local algebras extend each minimal
prime ideal of the source to the same ideal of the target. -/
theorem FormallyHomotopic.map_minimalPrime {R S : CompleteLocalAlgCat Λ k}
    {f₁ f₂ : R ⟶ S} (h : FormallyHomotopic f₁ f₂) {p : Ideal R.carrier}
    (hp : IsMinimalPrime p) :
    p.map f₁.hom = p.map f₂.hom := sorry

end CompleteLocalAlgCat
