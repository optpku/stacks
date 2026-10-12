/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import StacksCheckRecall

@[expose] public section

universe u v

namespace ProjectiveSpectrum

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]

/- Exercise 111.27.9 (1): the projective spectrum is empty when all sufficiently
high graded pieces vanish. -/
@[stacks 02EE] #check (ProjectiveSpectrum.isEmpty_of_eventually_zero :
  ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜],
    (∃ N, ∀ n, N ≤ n → ∀ x ∈ 𝒜 n, x = 0) → IsEmpty (ProjectiveSpectrum 𝒜))

/- Exercise 111.27.9 (2): a graded domain with nonzero irrelevant ideal has
irreducible projective spectrum; in particular, this space is nonempty. -/
@[stacks 02EE] #check (ProjectiveSpectrum.irreducibleSpace_of_isDomain :
  ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsDomain A],
    HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥ → IrreducibleSpace (ProjectiveSpectrum 𝒜))

end ProjectiveSpectrum
