module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.StandardOpenCover
import StacksCheckRecall

@[expose] public section

/-!
# Standard-open covers of `Proj`

The reusable owner for standard-open covers of an arbitrary projective spectrum
lives in `ReasLib.AlgebraicGeometry.ProjectiveSpectrum.StandardOpenCover`.
-/

open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

universe u v w

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (f : A)

/- Definition 27.8.2: for a homogeneous positive-degree element `f` of a graded ring, a standard
open cover of `D₊(f)` is a finite family of homogeneous positive-degree standard opens whose
union is `D₊(f)`. -/
@[stacks 01M5] #check
  (AlgebraicGeometry.Proj.StandardOpenCoverOf.{u, v, w} 𝒜 f : Type (max u (w + 1)))

#check
  (AlgebraicGeometry.Proj.StandardOpenCoverOf.opens :
    (𝒰 : AlgebraicGeometry.Proj.StandardOpenCoverOf 𝒜 f) →
      𝒰.index → TopologicalSpace.Opens (Proj 𝒜))

#check
  (AlgebraicGeometry.Proj.StandardOpenCoverOf.opens_apply :
    (𝒰 : AlgebraicGeometry.Proj.StandardOpenCoverOf 𝒜 f) →
      (i : 𝒰.index) → 𝒰.opens i = Proj.basicOpen 𝒜 (𝒰.generator i))

#check
  (AlgebraicGeometry.Proj.StandardOpenCoverOf.generator_spec :
    (𝒰 : AlgebraicGeometry.Proj.StandardOpenCoverOf 𝒜 f) →
      (i : 𝒰.index) →
        𝒰.generator i ∈ 𝒜 (𝒰.degree i) ∧ 0 < 𝒰.degree i)

#check
  (AlgebraicGeometry.Proj.StandardOpenCoverOf.iSup_eq :
    (𝒰 : AlgebraicGeometry.Proj.StandardOpenCoverOf 𝒜 f) →
      (⨆ i, 𝒰.opens i) = Proj.basicOpen 𝒜 f)

#check
  (AlgebraicGeometry.Proj.StandardOpenCoverOf.le :
    (𝒰 : AlgebraicGeometry.Proj.StandardOpenCoverOf 𝒜 f) →
      (i : 𝒰.index) → 𝒰.opens i ≤ Proj.basicOpen 𝒜 f)

#check
  (AlgebraicGeometry.Proj.StandardOpenCoverOf.spec :
    (𝒰 : AlgebraicGeometry.Proj.StandardOpenCoverOf 𝒜 f) →
      (f ∈ 𝒜 𝒰.fDegree ∧ 0 < 𝒰.fDegree) ∧
        (∀ i : 𝒰.index, 𝒰.generator i ∈ 𝒜 (𝒰.degree i) ∧ 0 < 𝒰.degree i) ∧
        Proj.basicOpen 𝒜 f = ⨆ i : 𝒰.index, Proj.basicOpen 𝒜 (𝒰.generator i))

end AlgebraicGeometry.Proj
