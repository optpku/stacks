/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.FromSections
public import stacks_project.Chap27.«27_12_0_3»
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {Y : Scheme.{u}}

/-- The tensor-power section ring of a module sheaf. -/
abbrev tensorPowerSectionRing {X : Scheme.{u}} (ℒ : X.Modules) : Type u :=
  RingedSpace.GradedSections.ring ℒ

/-- The chosen degree twist, first restricted to the degree open and then pulled back along a
morphism to that open. -/
noncomputable abbrev degreeOpenTwistPullback (d : ℕ)
    (φd : Y ⟶ (Proj.degreeOpen 𝒜 d).toScheme) (P : ProjTwistPresentation 𝒜) : Y.Modules :=
  (Scheme.Modules.pullback φd).obj
    ((Scheme.Modules.pullback (Proj.degreeOpen 𝒜 d).ι).obj (P.actualTwist d))

/-- A Veronese section map agrees with the map induced by a raw morphism to a degree open and
an isomorphism from its pulled-back degree twist. -/
def veroneseSectionMapCompatibleWithPresentation (d : ℕ) (ℒ : Y.Modules)
    (ψ : GradedRing.Veronese 𝒜 d →+* RingedSpace.GradedSections.ring ℒ)
    (φd : Y ⟶ (Proj.degreeOpen 𝒜 d).toScheme) (P : ProjTwistPresentation 𝒜)
    (α : degreeOpenTwistPullback 𝒜 d φd P ≅ ℒ) : Prop :=
  ∀ hd : 1 ≤ d,
    let x : Proj.DegreeOpenFactorization 𝒜 Y :=
      { degree := d, positive := hd, map := φd }
    Proj.DegreeOpenFactorization.SectionMapCompatible 𝒜 P x ℒ ψ
      (((Scheme.Modules.pullbackComp φd (Proj.degreeOpen 𝒜 d).ι).app
        (P.actualTwist d)).symm.trans α)

/- Lemma 27.12.1: a grading-preserving map from the `d`th Veronese ring whose degree-one
sections generate an invertible module determines a unique morphism to the degree-`d` open of
`Proj 𝒜` and a unique compatible isomorphism from the pulled-back degree twist. -/
@[stacks 01N8] #check
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

end AlgebraicGeometry
