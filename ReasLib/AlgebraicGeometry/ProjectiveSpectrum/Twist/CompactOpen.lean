/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.RatioOpenSections

/-!
# Compact opens and projective twisting sheaves

Compact opens of a projective spectrum lie in a ratio open of some positive degree. On every
open contained in such a ratio open, canonical twists and their standard maps retain the
invertibility, isomorphism, and nonvanishing-open properties needed to describe the topology.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section CompactContainment

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Every compact open of a projective spectrum is contained in the ratio open of some positive
degree. -/
theorem exists_pos_projTwistRatioOpen_containing_of_isCompact
    (Y : (Proj 𝒜).Opens) (hY : IsCompact (Y : Set (Proj 𝒜))) :
    ∃ d : ℕ, 0 < d ∧ Y ≤ projTwistRatioOpen 𝒜 d := sorry

end CompactContainment

section CanonicalTwists

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- A multiple of a positive ratio degree gives an invertible canonical twist after restriction
to every open contained in the ratio open. -/
theorem projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
    {d : ℕ} (hd : 0 < d) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) (n : ℤ) :
    Scheme.Modules.Invertible
      ((Scheme.Modules.restrictFunctor Y.ι).obj
        (Proj.AssociatedModule.twistingSheaf 𝒜 (n * (d : ℤ)))) := sorry

/-- Canonical twist multiplication with first index a multiple of a positive ratio degree is an
isomorphism after restriction to every open contained in the ratio open. -/
theorem projTwistMul_restrict_open_isIso_of_le_projTwistRatioOpen
    (T : Proj.AssociatedModule.TwistMultiplication 𝒜)
    {d : ℕ} (hd : 0 < d) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) (n m : ℤ) :
    IsIso
      (Proj.AssociatedModule.TwistMultiplication.restrictOpenMap
        𝒜 T Y (n * (d : ℤ)) m) := sorry

namespace Proj.AssociatedModule

/-- On an open contained in a positive-degree ratio open, the nonvanishing open of the canonical
section determined by a homogeneous element is the inverse image of its projective basic open. -/
theorem sectionNonvanishingOpen_twistSectionOnOpen_of_le_ratioOpen
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) (f : 𝒜 (n * d)) :
    (Eq.mp
      (congrArg
        (fun k : ℤ => Scheme.Modules.Invertible
          ((Scheme.Modules.restrictFunctor Y.ι).obj
            (Proj.AssociatedModule.twistingSheaf 𝒜 k)))
        (Int.natCast_mul n d).symm)
      (projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
        𝒜 hd hY (n : ℤ))).sectionNonvanishingOpen
        (Proj.AssociatedModule.twistSectionOnOpen 𝒜 Y f) =
      Y.ι ⁻¹ᵁ Proj.basicOpen 𝒜 (f : A) := sorry

end Proj.AssociatedModule

/-- The nonvanishing opens of all global sections of the positive multiples of a canonical twist
degree form a basis on every open contained in the corresponding ratio open. -/
theorem isBasis_projTwistSectionNonvanishingOpen_of_le_projTwistRatioOpen
    {d : ℕ} (hd : 0 < d) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) :
    TopologicalSpace.Opens.IsBasis
      {U : Y.toScheme.Opens |
        ∃ n : ℕ+,
          ∃ s : Γ((Scheme.Modules.restrictFunctor Y.ι).obj
              (Proj.AssociatedModule.twistingSheaf 𝒜 ((n : ℤ) * (d : ℤ))), ⊤),
            U = (projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
              𝒜 hd hY (n : ℤ)).sectionNonvanishingOpen s} := sorry

/-- The affine nonvanishing opens among all global sections of the positive multiples of a
canonical twist degree form a basis on every open contained in the corresponding ratio open. -/
theorem isBasis_affine_projTwistSectionNonvanishingOpen_of_le_projTwistRatioOpen
    {d : ℕ} (hd : 0 < d) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) :
    TopologicalSpace.Opens.IsBasis
      {U : Y.toScheme.Opens |
        ∃ n : ℕ+,
          ∃ s : Γ((Scheme.Modules.restrictFunctor Y.ι).obj
              (Proj.AssociatedModule.twistingSheaf 𝒜 ((n : ℤ) * (d : ℤ))), ⊤),
            U = (projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
                𝒜 hd hY (n : ℤ)).sectionNonvanishingOpen s ∧
              IsAffineOpen U} := sorry

end CanonicalTwists

namespace Proj.AssociatedModule.ShiftComparison

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

/-- A standard shift comparison at an index divisible by a positive ratio degree is an
isomorphism after restriction to every open contained in the ratio open. -/
theorem restrictOpen_isIso_of_le_projTwistRatioOpen
    (C : Proj.AssociatedModule.ShiftComparison 𝒜 ℳ)
    {d : ℕ} (hd : 0 < d) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) (n : ℤ) :
    IsIso (restrictOpenMap 𝒜 ℳ C Y (n * (d : ℤ))) := sorry

end Proj.AssociatedModule.ShiftComparison

end AlgebraicGeometry
