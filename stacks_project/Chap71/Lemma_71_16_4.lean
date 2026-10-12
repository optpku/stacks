/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_16_4_Conormal
public import stacks_project.Chap71.Lemma_71_16_4_Lift
public import stacks_project.Chap71.Lemma_71_16_4_Presentation
public import stacks_project.Chap71.Lemma_71_16_4_Quotient
public import stacks_project.Chap76.Definition_76_6_5_Conormal

/-!
# Lemma 71.16.4

Sections of the projective bundle of a quasi-coherent module on an algebraic
space correspond to invertible quotient classes; each such section is a closed
immersion, and the kernel-tensor-inverse of the quotient is canonically the
conormal sheaf of the section. Both the bijection and the comparison are
compatible with base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.InvertibleQuotient
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace
namespace ProjectiveBundle
namespace SymmetricPresentation

variable {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
variable {π : P ⟶ X}

/-- Lemma 71.16.4 (1): sections of a symmetric projective bundle of a quasi-coherent
module `ℰ` on an algebraic space correspond bijectively to invertible quotient classes
of `ℰ`. -/
@[stacks 0B4I]
theorem sectionToQuotientClass_bijective (Pres : SymmetricPresentation π ℰ) :
    Function.Bijective Pres.sectionToQuotientClass := sorry

/-- Lemma 71.16.4 (2): the lift-to-quotient-class correspondence commutes with arbitrary
precomposition. -/
@[stacks 0B4I]
theorem liftToQuotientClass_naturality (Pres : SymmetricPresentation π ℰ)
    {T R : AlgebraicSpace S} (f : T ⟶ X) (σ : Lift π f) (g : R ⟶ T) :
    Pres.liftToQuotientClass (g ≫ f) (σ.precomp g) =
      quotientPointMap f g (Pres.liftToQuotientClass f σ) := sorry

section
variable (Pres : SymmetricPresentation π ℰ)

/-- Lemma 71.16.4 (3): every section of a symmetric projective-bundle presentation is a
closed immersion. -/
@[stacks 0B4I]
instance section_isClosedImmersion (σ : Lift π (𝟙 X)) : IsClosedImmersion σ.hom :=
  sorry

end

/-- Lemma 71.16.4 (4): a quotient representative corresponding to a section has a canonical
conormal morphism whose target is the conormal sheaf of the section in the original
projective bundle. -/
@[stacks 0B4I]
def sectionConormalMap (Pres : SymmetricPresentation π ℰ)
    (σ : Lift π (𝟙 X)) (q : InvertibleQuotient ℰ)
    (h : IsoClass.mk q = Pres.sectionToQuotientClass σ) :
    conormalObject q ⟶ Hom.conormalSheaf σ.hom :=
  (sectionPullbackConormalIso q).hom ≫
    Pres.liftConormalMap σ (sectionPullbackQuotient q)
      (Pres.sectionPullbackQuotient_class σ q h) ≫
    sectionConormalTransport σ

/-- Lemma 71.16.4 (5): the canonical conormal morphism of a section is an isomorphism. -/
@[stacks 0B4I]
theorem sectionConormalMap_isIso (Pres : SymmetricPresentation π ℰ)
    (σ : Lift π (𝟙 X)) (q : InvertibleQuotient ℰ)
    (h : IsoClass.mk q = Pres.sectionToQuotientClass σ) :
    IsIso (sectionConormalMap Pres σ q h) := sorry

/-- Lemma 71.16.4 (6): the explicit conormal morphisms commute with arbitrary base change,
with the pulled-back representative and its class equality constructed canonically. -/
@[stacks 0B4I]
theorem liftConormalMap_precomp (Pres : SymmetricPresentation π ℰ)
    {T R : AlgebraicSpace S} (f : T ⟶ X) (σ : Lift π f) (g : R ⟶ T)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ))
    (h : IsoClass.mk q = IsoClass.mk (Pres.liftSourceQuotient σ)) :
    (Modules.pullback g).map (Pres.liftConormalMap σ q h) ≫
        precompConormalSheafMap σ g =
      liftConormalPullbackComparison g q ≫
        Pres.liftConormalMap (σ.precomp g) (pullbackRepresentative g q)
          (Pres.pullbackRepresentative_class σ g q h) := sorry

end SymmetricPresentation
end ProjectiveBundle
end AlgebraicSpace
end AlgebraicGeometry
