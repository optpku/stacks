module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ProjFromSections
public import stacks_project.Chap27.Lemma_27_12_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {T : Scheme.{u}} (L : T.Modules) [Scheme.Modules.Invertible L]

/-- The stalkwise nonvanishing locus of a global section of a scheme module. -/
abbrev sectionNonvanishingSet (M : T.Modules) (s : Γ(M, ⊤)) : Set T :=
  RingedSpace.sectionNonvanishingLocus T.toRingedSpace M
    (RingedSpace.sectionFromTop M s)

/- Lemma 27.14.1 (1): a graded homomorphism into the tensor-power section ring of an invertible
module determines a unique complete canonical morphism from its natural domain to `Proj 𝒜`,
together with the canonical comparison of integral graded algebra sheaves. -/
@[stacks 01NK] #check
  (Scheme.Modules.existsUnique_projSectionMap 𝒜 :
    ∀ (L : T.Modules) [Scheme.Modules.Invertible L]
      (P : ProjTwistPresentation 𝒜)
      (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L),
      ∃! c : Scheme.Modules.ProjSectionMap 𝒜 L P ψ,
        Scheme.Modules.ProjSectionMap.IsCanonical c)

/- Lemma 27.14.1 (2): on an open where the positive degree-`d` image generates, the canonical
morphism and its degree-`d` comparison agree with the unique degree-open morphism and twist
isomorphism attached to the restricted Veronese section map. -/
@[stacks 01NK] #check
  (Scheme.Modules.ProjSectionMap.IsCanonical.restrict_eq_degreeOpenMorphismAndTwistIso :
    ∀ {L : T.Modules} [Scheme.Modules.Invertible L]
      {P : ProjTwistPresentation 𝒜}
      {ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L}
      {c : Scheme.Modules.ProjSectionMap 𝒜 L P ψ},
      Scheme.Modules.ProjSectionMap.IsCanonical c →
        ∀ (V : T.Opens) (d : ℕ) (hd : 1 ≤ d)
          (_ : veroneseDegreeOneImageGenerates 𝒜 d
            (Scheme.Modules.restrictedVeroneseLineBundle L V d)
              (Scheme.Modules.restrictedVeroneseSectionMap 𝒜 L ψ V d)),
              ∃ hV : V ≤ Scheme.Modules.projSectionMapDomain 𝒜 L ψ,
                ∃! φd : V.toScheme ⟶ (Proj.degreeOpen 𝒜 d).toScheme,
                  let x : Proj.DegreeOpenFactorization 𝒜 V.toScheme :=
                    { degree := d, positive := hd, map := φd }
                  ∃! α : Proj.DegreeOpenFactorization.lineBundle 𝒜 P x ≅
                      Scheme.Modules.restrictedVeroneseLineBundle L V d,
                    Proj.DegreeOpenFactorization.SectionMapCompatible 𝒜 P x
                        (Scheme.Modules.restrictedVeroneseLineBundle L V d)
                          (Scheme.Modules.restrictedVeroneseSectionMap 𝒜 L ψ V d) α ∧
                      ∃ hcomp : T.homOfLE hV ≫ c.map =
                          φd ≫ (Proj.degreeOpen 𝒜 d).ι,
                        c.restrictedComponent V hV d hd hcomp = α.hom)

end AlgebraicGeometry
