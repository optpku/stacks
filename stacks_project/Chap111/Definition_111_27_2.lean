/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Definition
import StacksCheckRecall

@[expose] public section

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Definition 111.27.2: the homogeneous spectrum `Proj(R)` of a graded ring is the set of
homogeneous prime ideals `𝔭` such that `R₊ ⊈ 𝔭`. This is the canonical type
`ProjectiveSpectrum 𝒜` of relevant homogeneous primes. A point `x : ProjectiveSpectrum 𝒜`
determines the prime `⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩ : PrimeSpectrum A`, so `Proj`
is a subset of `Spec`. The induced topology is the canonical instance
`ProjectiveSpectrum.zariskiTopology`, whose closed sets are the zero loci `V(I) ∩ Proj`. -/
@[stacks 0282] #check (ProjectiveSpectrum.homogeneousSpectrum 𝒜 : Set (HomogeneousIdeal 𝒜))
#check (ProjectiveSpectrum 𝒜 : Type _)
#check (ProjectiveSpectrum.asHomogeneousIdeal : ProjectiveSpectrum 𝒜 → HomogeneousIdeal 𝒜)
#check (ProjectiveSpectrum.isPrime :
  ∀ point : ProjectiveSpectrum 𝒜, point.asHomogeneousIdeal.toIdeal.IsPrime)
#check (ProjectiveSpectrum.not_irrelevant_le :
  ∀ point : ProjectiveSpectrum 𝒜, ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ point.asHomogeneousIdeal)
#check (HomogeneousIdeal.irrelevant 𝒜 : HomogeneousIdeal 𝒜)
#check (ProjectiveSpectrum.zariskiTopology 𝒜 : TopologicalSpace (ProjectiveSpectrum 𝒜))

end
