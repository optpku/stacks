module

public import stacks_project.Chap90.Lemma_90_28_2_FormalHomotopy

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Lemma 90.28.2: in the category CompleteLocalAlgCat Λ k, if f₁, f₂ : R ⟶ S are
formally homotopic and g : S ⟶ S' is a morphism, then f₁ ≫ g and f₂ ≫ g are
formally homotopic. -/
@[stacks 0DQC]
theorem FormallyHomotopic.compRight {R S S' : CompleteLocalAlgCat Λ k}
    {f₁ f₂ : R ⟶ S} (h : FormallyHomotopic f₁ f₂) (g : S ⟶ S') :
    FormallyHomotopic (f₁ ≫ g) (f₂ ≫ g) := sorry

end CompleteLocalAlgCat
