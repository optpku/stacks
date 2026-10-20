module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOpen
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u
universe v

namespace AlgebraicGeometry.Proj

variable {σ : Type v} {A : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

#check (AlgebraicGeometry.Proj.degreeOpen :
  ∀ {σ : Type v} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ), (AlgebraicGeometry.Proj 𝒜).Opens)

/- 27.12.0.1: For `X = Proj 𝒜`, the open `U_d` is the union of the basic opens `D₊(f)`
over all `f ∈ 𝒜 d`. -/
@[stacks 01N5] #check (AlgebraicGeometry.Proj.degreeOpen_eq_iSup :
  ∀ {σ : Type v} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ), AlgebraicGeometry.Proj.degreeOpen 𝒜 d =
      ⨆ (f : A) (hf : f ∈ 𝒜 d), AlgebraicGeometry.Proj.basicOpen 𝒜 f)

#check (AlgebraicGeometry.Proj.basicOpen_le_degreeOpen :
  ∀ {σ : Type v} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {f : A}, f ∈ 𝒜 d →
      AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ AlgebraicGeometry.Proj.degreeOpen 𝒜 d)

end AlgebraicGeometry.Proj
