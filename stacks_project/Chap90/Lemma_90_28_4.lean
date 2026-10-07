module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import stacks_project.Chap90.Lemma_90_28_2_FormalHomotopy

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Lemma 90.28.4: in the category CompleteLocalAlgCat Λ k, if f₁, f₂ : R ⟶ S are
formally homotopic and p ⊂ R is a minimal prime ideal, then f₁(p)S = f₂(p)S as
ideals. -/
@[stacks 0DQE]
theorem FormallyHomotopic.map_minimalPrime {R S : CompleteLocalAlgCat Λ k}
    {f₁ f₂ : R ⟶ S} (h : FormallyHomotopic f₁ f₂) {p : Ideal R.carrier}
    (hp : IsMinimalPrime p) :
    p.map f₁.hom = p.map f₂.hom := sorry

end CompleteLocalAlgCat
