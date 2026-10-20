/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.RatioOpen

/-!
# Twist sections on ratio opens

This module relates canonical twisting-sheaf sections on ratio opens to projective basic opens.
-/

@[expose] public section

open AlgebraicGeometry
open Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- A positive ratio degree makes the canonical twist indexed by a natural multiple invertible
after restriction to the corresponding ratio open. -/
theorem projTwist_restrict_ratioOpen_invertible_nat_mul
    (d n : ℕ) (hd : 0 < d) :
    Scheme.Modules.Invertible
      ((Scheme.Modules.restrictFunctor (projTwistRatioOpen 𝒜 d).ι).obj
        (Proj.AssociatedModule.twistingSheaf 𝒜 ((n * d : ℕ) : ℤ))) := sorry

/-- On a positive-degree ratio open, the nonvanishing open of a restricted canonical twist
section is the inverse image of the projective basic open defined by its homogeneous element. -/
theorem projTwistRatioOpen_sectionNonvanishingOpen_eq_preimage_basicOpen
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (f : 𝒜 (n * d)) :
    (projTwist_restrict_ratioOpen_invertible_nat_mul 𝒜 d n hd).sectionNonvanishingOpen
        (Proj.AssociatedModule.twistSectionOnOpen 𝒜 (projTwistRatioOpen 𝒜 d) f) =
      (projTwistRatioOpen 𝒜 d).ι ⁻¹ᵁ Proj.basicOpen 𝒜 (f : A) := sorry

end AlgebraicGeometry
