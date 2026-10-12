/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GradedSections
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry

section

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (Mpiece : ℤ → Type u) [∀ n : ℤ, AddCommGroup (Mpiece n)]
variable (P : AlgebraicGeometry.Proj.AssociatedModule.Presentation 𝒜 Mpiece) (n : ℤ)

/- 27.9.0.2: The canonical map from the degree-`n` piece of a graded module to the global
sections of its associated `n`th twist on `Proj`. -/
@[stacks 0AG2] #check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.sectionMap P n :
    Mpiece n →+ Γ(P.associatedTwist n, ⊤))

end

end AlgebraicGeometry
