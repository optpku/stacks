/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

@[expose] public section

universe u v

namespace HomogeneousLocalization.Away

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The homogeneous localization embeds as a subring of the ordinary localization at powers of `f`. -/
def subring (f : A) : Subring (Localization (Submonoid.powers f)) :=
  (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization (Submonoid.powers f))).range

/-- Membership in the homogeneous-localization subring is represented by a homogeneous fraction. -/
theorem mem_subring_iff {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
    (z : Localization (Submonoid.powers f)) :
    z ∈ subring 𝒜 f ↔
      ∃ (n : ℕ) (r : A), r ∈ 𝒜 (n * d) ∧
        z = Localization.mk r (Submonoid.pow f n) := sorry

end HomogeneousLocalization.Away
