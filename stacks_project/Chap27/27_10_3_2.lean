module

import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GradedSections
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry DirectSum

universe u v

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (Mpiece : ℤ → Type u) [∀ n : ℤ, AddCommGroup (Mpiece n)]
variable (P : AlgebraicGeometry.Proj.AssociatedModule.Presentation 𝒜 Mpiece)
variable [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) Mpiece]
variable [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
  (fun n : ℤ ↦ Γ(P.associatedTwist n, ⊤))]
variable (hP : P.IsGraded)
variable {𝒜}

/- 27.10.3.2: The canonical graded-module map
`M ⟶ ⨁ n : ℤ, Γ(X, ~(M(n)))`. -/
@[stacks 0AG4] #check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.gradedMap Mpiece P hP :
    (⨁ n : ℤ, Mpiece n) →ₗ[(⨁ d : ℕ, 𝒜 d)]
      (⨁ n : ℤ, Γ(P.associatedTwist n, ⊤)))
