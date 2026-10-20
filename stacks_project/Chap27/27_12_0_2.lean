/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.DegreeOpenSections
public import stacks_project.Chap27.«27_12_0_1»
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A coherent comparison between the pulled-back twists on a fixed degree open and tensor
powers of its degree-`d` twist. -/
abbrev DegreeOpenPsiComparison (P : ProjTwistPresentation 𝒜) (d : ℕ) (hd : 1 ≤ d) :=
  Proj.DegreeOpenFactorization.TwistComparison 𝒜 P
    (Proj.DegreeOpenFactorization.ofDegreeOpen 𝒜 d hd)

/-- The Veronese-to-section-ring homomorphism on a fixed degree open, expressed using a coherent
comparison with tensor powers of the degree-`d` twist. -/
abbrev degreeOpenPsiTensorModel (P : ProjTwistPresentation 𝒜) (d : ℕ) (hd : 1 ≤ d)
    (comparison : DegreeOpenPsiComparison 𝒜 P d hd) :
    GradedRing.Veronese 𝒜 d →+*
      RingedSpace.GradedSections.ring
        (Proj.DegreeOpenFactorization.lineBundle 𝒜 P
          (Proj.DegreeOpenFactorization.ofDegreeOpen 𝒜 d hd)) :=
  Proj.DegreeOpenFactorization.psi 𝒜 P
    (Proj.DegreeOpenFactorization.ofDegreeOpen 𝒜 d hd) comparison

variable (P : ProjTwistPresentation 𝒜) (d : ℕ) (hd : 1 ≤ d)
variable (comparison : DegreeOpenPsiComparison 𝒜 P d hd)

/- 27.12.0.2: the d-Veronese ring maps to the tensor-power section ring
Γ_*(U_d, 𝒪_{U_d}(d)) on the fixed degree open U_d = Proj.degreeOpen 𝒜 d. -/
@[stacks 01N6] #check
  (AlgebraicGeometry.Proj.DegreeOpenFactorization.psi 𝒜 P
      (AlgebraicGeometry.Proj.DegreeOpenFactorization.ofDegreeOpen 𝒜 d hd) comparison :
    GradedRing.Veronese 𝒜 d →+*
      AlgebraicGeometry.RingedSpace.GradedSections.ring
        (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P
          (AlgebraicGeometry.Proj.DegreeOpenFactorization.ofDegreeOpen 𝒜 d hd)))

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.psi_of :
  ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    (P : AlgebraicGeometry.ProjTwistPresentation 𝒜)
    (x : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y)
    (comparison : AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison 𝒜 P x)
    (n : ℕ) (a : GradedRing.Veronese.degree 𝒜 x.degree n),
    AlgebraicGeometry.Proj.DegreeOpenFactorization.psi 𝒜 P x comparison
        (DirectSum.of (GradedRing.Veronese.degree 𝒜 x.degree) n a) =
      DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
        (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) n
        ((AlgebraicGeometry.Proj.DegreeOpenFactorization.psiDegreeMap
          𝒜 P x comparison n).hom a))

end

end AlgebraicGeometry
