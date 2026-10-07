module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.MorphismDatum
public import stacks_project.Chap27.Lemma_27_12_2

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {Y : Scheme.{u}}

/-- The source-facing name for degree-one projective-spectrum morphism data. -/
abbrev DegreeOneProjDatum (Y : Scheme.{u}) := Proj.DegreeOneMorphismDatum 𝒜 Y

namespace DegreeOneProjDatum

/-- Association of source-facing degree-one data with a morphism to the projective spectrum. -/
abbrev AssociatedTo (tau : DegreeOneProjDatum 𝒜 Y) (phi : Y ⟶ Proj 𝒜) : Prop :=
  Proj.DegreeOneMorphismDatum.AssociatedTo 𝒜 tau phi

end DegreeOneProjDatum

end AlgebraicGeometry

section

open CategoryTheory

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {Y : AlgebraicGeometry.Scheme.{u}}

/- Lemma 27.12.3: if a graded ring is generated over its degree-zero piece by its degree-one
piece, then strict-equivalence classes of invertible modules with generating degree-preserving
section maps and morphisms to its projective spectrum determine one another uniquely. -/
@[stacks 01NA] #check
  (AlgebraicGeometry.Proj.DegreeOneMorphismDatumClass.associatedTo_bijective 𝒜 :
    GradedAlgebra.GeneratedBy 𝒜 1 →
      (∀ tau : AlgebraicGeometry.Proj.DegreeOneMorphismDatumClass 𝒜 Y,
        ∃! phi : Y ⟶ AlgebraicGeometry.Proj 𝒜,
          AlgebraicGeometry.Proj.DegreeOneMorphismDatumClass.AssociatedTo 𝒜 tau phi) ∧
      (∀ phi : Y ⟶ AlgebraicGeometry.Proj 𝒜,
        ∃! tau : AlgebraicGeometry.Proj.DegreeOneMorphismDatumClass 𝒜 Y,
          AlgebraicGeometry.Proj.DegreeOneMorphismDatumClass.AssociatedTo 𝒜 tau phi))

end
