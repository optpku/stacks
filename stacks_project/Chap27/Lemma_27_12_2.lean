module

import StacksCheckRecall
public import stacks_project.Chap27.«27_12_0_2»
public import stacks_project.Chap27.Lemma_27_12_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

section

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {Y : Scheme.{u}}

/- Lemma 27.12.2: let `S` be a graded ring, let `X = Proj(S)`, and let
`U_d = AlgebraicGeometry.Proj.degreeOpen 𝒜 d ⊆ X` be the degree-`d` open from `27.12.0.1`.
The source states that `U_d` represents the chart functor `F_d`, and that the triple
`(d, 𝒪_{U_d}(d), ψ^d)` is the universal family.

The source itself says this is a reformulation of Lemma 27.12.1. In the current local API, the
representing property is exactly the theorem
`existsUnique_degreeOpenMorphismAndTwistIso_of_veroneseSectionMap`, while the explicit universal
family is the Chapter 27 construction `degreeOpenPsiTensorModel` on `U_d`. Accordingly this item
is recorded as a canonical check rather than a duplicate local wrapper theorem. -/
@[stacks 01N9] #check
  (AlgebraicGeometry.existsUnique_degreeOpenMorphismAndTwistIso_of_veroneseSectionMap 𝒜 :
    ∀ (P : ProjTwistPresentation 𝒜) (d : ℕ) (hd : 1 ≤ d)
      (ℒ : Y.Modules) [Scheme.Modules.Invertible ℒ]
      (ψ : GradedRing.Veronese 𝒜 d →+* RingedSpace.GradedSections.ring ℒ),
      veroneseSectionMapPreservesDegree 𝒜 d ℒ ψ →
        veroneseDegreeOneImageGenerates 𝒜 d ℒ ψ →
          ∃! φd : Y ⟶ (Proj.degreeOpen 𝒜 d).toScheme,
            let x : Proj.DegreeOpenFactorization 𝒜 Y :=
              { degree := d, positive := hd, map := φd }
            ∃! α : Proj.DegreeOpenFactorization.lineBundle 𝒜 P x ≅ ℒ,
              Proj.DegreeOpenFactorization.SectionMapCompatible 𝒜 P x ℒ ψ α)

#check AlgebraicGeometry.DegreeOpenPsiComparison
#check AlgebraicGeometry.degreeOpenPsiTensorModel

end
