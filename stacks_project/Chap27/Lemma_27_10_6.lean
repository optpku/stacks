/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CompactOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 27.10.6 (1): every quasi-compact open of `Proj(𝒜)` is contained in
`projTwistRatioOpen 𝒜 d` for some positive `d`. -/
@[stacks 01MW] #check
  (AlgebraicGeometry.exists_pos_projTwistRatioOpen_containing_of_isCompact :
    ∀ {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
      (𝒜 : ℕ → σ) [GradedRing 𝒜]
      (Y : (AlgebraicGeometry.Proj 𝒜).Opens),
      IsCompact (Y : Set (AlgebraicGeometry.Proj 𝒜)) →
        ∃ d : ℕ, 0 < d ∧ Y ≤ AlgebraicGeometry.projTwistRatioOpen 𝒜 d)

/- For a positive `d` and `Y ≤ projTwistRatioOpen 𝒜 d`, every restricted canonical twist of
index `n * d` is invertible. -/
#check
  (AlgebraicGeometry.projTwist_restrict_open_invertible_of_le_projTwistRatioOpen :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      {d : ℕ} (hd : 0 < d) {Y : (AlgebraicGeometry.Proj 𝒜).Opens}
      (hY : Y ≤ AlgebraicGeometry.projTwistRatioOpen 𝒜 d) (n : ℤ),
      AlgebraicGeometry.Scheme.Modules.Invertible
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor Y.ι).obj
          (AlgebraicGeometry.Proj.AssociatedModule.twistingSheaf
            𝒜 (n * (d : ℤ)))))

/- For a positive `d` and `Y ≤ projTwistRatioOpen 𝒜 d`, canonical multiplication from the
restricted twists of indices `n * d` and `m` to the twist of index `n * d + m` is an
isomorphism. -/
#check
  (AlgebraicGeometry.projTwistMul_restrict_open_isIso_of_le_projTwistRatioOpen :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (T : AlgebraicGeometry.Proj.AssociatedModule.TwistMultiplication 𝒜)
      {d : ℕ} (hd : 0 < d) {Y : (AlgebraicGeometry.Proj 𝒜).Opens}
      (hY : Y ≤ AlgebraicGeometry.projTwistRatioOpen 𝒜 d) (n m : ℤ),
      IsIso
        (AlgebraicGeometry.Proj.AssociatedModule.TwistMultiplication.restrictOpenMap
          𝒜 T Y (n * (d : ℤ)) m))

/- For a graded module, its specified shift comparison restricted to
`Y ≤ projTwistRatioOpen 𝒜 d` is an isomorphism at every index `n * d`. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison.restrictOpen_isIso_of_le_projTwistRatioOpen :
    ∀ {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]
      (C : AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison 𝒜 ℳ)
      {d : ℕ} (hd : 0 < d) {Y : (AlgebraicGeometry.Proj 𝒜).Opens}
      (hY : Y ≤ AlgebraicGeometry.projTwistRatioOpen 𝒜 d) (n : ℤ),
      IsIso
        (AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison.restrictOpenMap
          𝒜 ℳ C Y (n * (d : ℤ))))

/- If `f` is homogeneous of positive degree `n * d`, the nonvanishing open of its canonical
section on `Y ≤ projTwistRatioOpen 𝒜 d` is `Y.ι ⁻¹ᵁ Proj.basicOpen 𝒜 f`. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.sectionNonvanishingOpen_twistSectionOnOpen_of_le_ratioOpen :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
      {Y : (AlgebraicGeometry.Proj 𝒜).Opens}
      (hY : Y ≤ AlgebraicGeometry.projTwistRatioOpen 𝒜 d) (f : 𝒜 (n * d)),
      (Eq.mp
        (congrArg
          (fun k : ℤ => AlgebraicGeometry.Scheme.Modules.Invertible
            ((AlgebraicGeometry.Scheme.Modules.restrictFunctor Y.ι).obj
              (AlgebraicGeometry.Proj.AssociatedModule.twistingSheaf 𝒜 k)))
          (Int.natCast_mul n d).symm)
        (AlgebraicGeometry.projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
          𝒜 hd hY (n : ℤ))).sectionNonvanishingOpen
          (AlgebraicGeometry.Proj.AssociatedModule.twistSectionOnOpen 𝒜 Y f) =
        Y.ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))

/- The nonvanishing opens of all global sections of the restricted twists of positive indices
`n * d` form a basis for the topology on `Y`. -/
#check
  (AlgebraicGeometry.isBasis_projTwistSectionNonvanishingOpen_of_le_projTwistRatioOpen :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      {d : ℕ} (hd : 0 < d) {Y : (AlgebraicGeometry.Proj 𝒜).Opens}
      (hY : Y ≤ AlgebraicGeometry.projTwistRatioOpen 𝒜 d),
      TopologicalSpace.Opens.IsBasis
        {U : Y.toScheme.Opens |
          ∃ n : ℕ+,
            ∃ s : Γ((AlgebraicGeometry.Scheme.Modules.restrictFunctor Y.ι).obj
                (AlgebraicGeometry.Proj.AssociatedModule.twistingSheaf
                  𝒜 ((n : ℤ) * (d : ℤ))), ⊤),
              U =
                (AlgebraicGeometry.projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
                  𝒜 hd hY (n : ℤ)).sectionNonvanishingOpen s})

/- The affine members of the same family of all positive-degree restricted-twist section
nonvanishing opens also form a basis for the topology on `Y`. -/
#check
  (AlgebraicGeometry.isBasis_affine_projTwistSectionNonvanishingOpen_of_le_projTwistRatioOpen :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      {d : ℕ} (hd : 0 < d) {Y : (AlgebraicGeometry.Proj 𝒜).Opens}
      (hY : Y ≤ AlgebraicGeometry.projTwistRatioOpen 𝒜 d),
      TopologicalSpace.Opens.IsBasis
        {U : Y.toScheme.Opens |
          ∃ n : ℕ+,
            ∃ s : Γ((AlgebraicGeometry.Scheme.Modules.restrictFunctor Y.ι).obj
                (AlgebraicGeometry.Proj.AssociatedModule.twistingSheaf
                  𝒜 ((n : ℤ) * (d : ℤ))), ⊤),
              U =
                  (AlgebraicGeometry.projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
                    𝒜 hd hY (n : ℤ)).sectionNonvanishingOpen s ∧
                AlgebraicGeometry.IsAffineOpen U})
