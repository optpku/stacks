module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.RatioOpenSections
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 27.10.5: for positive integers `d` and `n` and a homogeneous element `f` of degree
`n * d`, the canonical section of the corresponding twist on the ratio open `W_d` is nonzero
exactly over `D₊(f) ∩ W_d`. -/
@[stacks 01MV] #check
  (AlgebraicGeometry.projTwistRatioOpen_sectionNonvanishingOpen_eq_preimage_basicOpen :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (f : 𝒜 (n * d)),
      (AlgebraicGeometry.projTwist_restrict_ratioOpen_invertible_nat_mul
          𝒜 d n hd).sectionNonvanishingOpen
          (AlgebraicGeometry.Proj.AssociatedModule.twistSectionOnOpen 𝒜
            (AlgebraicGeometry.projTwistRatioOpen 𝒜 d) f) =
        (AlgebraicGeometry.projTwistRatioOpen 𝒜 d).ι ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
