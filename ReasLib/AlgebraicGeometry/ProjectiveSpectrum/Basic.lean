/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The canonical morphism from Proj to the degree-zero spectrum

This file records the pointwise action of the canonical morphism from the projective spectrum
of a graded ring to the spectrum of its degree-zero subring.
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The point of the degree-zero spectrum underlying the canonical morphism from `Proj` is
obtained by contracting the corresponding homogeneous prime ideal along the degree-zero
inclusion. -/
theorem toSpecZero_base_asIdeal (x : ProjectiveSpectrum 𝒜) :
    ((toSpecZero 𝒜).base x).asIdeal =
      Ideal.comap (algebraMap (𝒜 0) A) x.asHomogeneousIdeal.toIdeal := sorry

/-- The underlying map of the canonical morphism from `Proj` to the spectrum of the
degree-zero subring is continuous. -/
theorem toSpecZero_base_continuous : Continuous ((toSpecZero 𝒜).base) := sorry

end AlgebraicGeometry.Proj
