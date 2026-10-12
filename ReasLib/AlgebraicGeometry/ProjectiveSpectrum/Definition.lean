/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

@[expose] public section

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]

/-- The homogeneous spectrum of a graded commutative ring is the set of homogeneous prime
ideals that do not contain the irrelevant ideal. -/
def homogeneousSpectrum (𝒜 : ℕ → σ) [GradedRing 𝒜] : Set (HomogeneousIdeal 𝒜) :=
  {primeIdeal | primeIdeal.toIdeal.IsPrime ∧ ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ primeIdeal}

end ProjectiveSpectrum
