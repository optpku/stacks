/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.ConormalComparison
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 31.31.6 (1): for a quasi-coherent module `ℰ` on a scheme `X`, sections of its
symmetric projective bundle correspond bijectively to invertible quotient classes of `ℰ`. -/
@[stacks 0B3V] #check
  (AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.sectionToQuotientClass_bijective :
    ∀ {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent] {π : P ⟶ X}
      (S : ProjectiveBundle.SymmetricPresentation π ℰ),
      Function.Bijective S.sectionToQuotientClass)

/- Lemma 31.31.6 (2): the lift-to-quotient-class correspondence commutes with arbitrary
precomposition. -/
@[stacks 0B3V] #check
  (AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.liftToQuotientClass_naturality :
    ∀ {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent] {π : P ⟶ X}
      (S : ProjectiveBundle.SymmetricPresentation π ℰ) {T R : Scheme.{u}}
      (f : T ⟶ X) (σ : ProjectiveBundle.Lift π f) (g : R ⟶ T),
      S.liftToQuotientClass (g ≫ f) (σ.precomp g) =
        ProjectiveBundle.QuotientFunctor.quotientPointMap f g
          (S.liftToQuotientClass f σ))

/- Lemma 31.31.6 (3): every section of a symmetric projective-bundle presentation is a closed
immersion. -/
@[stacks 0B3V] #check
  (AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.section_isClosedImmersion :
    ∀ {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent] {π : P ⟶ X}
      (S : ProjectiveBundle.SymmetricPresentation π ℰ)
      (σ : ProjectiveBundle.Lift π (𝟙 X)), IsClosedImmersion σ.hom)

/- Lemma 31.31.6 (4): a quotient representative corresponding to a section has a canonical
conormal morphism whose target is the conormal sheaf of the section in the original projective
bundle. -/
@[stacks 0B3V] #check
  (AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.ConormalAtlas.sectionConormalMap :
    ∀ {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent] {π : P ⟶ X}
      (S : ProjectiveBundle.SymmetricPresentation π ℰ)
      (σ : ProjectiveBundle.Lift π (𝟙 X))
      (q : CategoryTheory.InvertibleQuotient ℰ)
      (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
        S.sectionToQuotientClass σ),
      CategoryTheory.InvertibleQuotient.conormalObject q ⟶
        Scheme.Hom.conormalSheaf σ.hom)

/- Lemma 31.31.6 (5): the canonical conormal morphism of a section is an isomorphism. -/
@[stacks 0B3V] #check
  (AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.ConormalAtlas.sectionConormalMap_isIso :
    ∀ {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent] {π : P ⟶ X}
      (S : ProjectiveBundle.SymmetricPresentation π ℰ)
      (σ : ProjectiveBundle.Lift π (𝟙 X))
      (q : CategoryTheory.InvertibleQuotient ℰ)
      (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
        S.sectionToQuotientClass σ),
      IsIso (ProjectiveBundle.SymmetricPresentation.ConormalAtlas.sectionConormalMap S σ q h))

/- Lemma 31.31.6 (6): the explicit conormal morphisms commute with arbitrary base change, with
the pulled-back representative and its class equality constructed canonically. -/
@[stacks 0B3V] #check
  (AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.ConormalAtlas.liftConormalMap_precomp :
    ∀ {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent] {π : P ⟶ X}
      (S : ProjectiveBundle.SymmetricPresentation π ℰ)
      {T R : Scheme.{u}} (f : T ⟶ X) (σ : ProjectiveBundle.Lift π f)
      (g : R ⟶ T)
      (q : CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ))
      (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
        CategoryTheory.InvertibleQuotient.IsoClass.mk (S.liftSourceQuotient f σ)),
      (Scheme.Modules.pullback g).map
            (ProjectiveBundle.SymmetricPresentation.ConormalAtlas.liftConormalMap S
              (ProjectiveBundle.SymmetricPresentation.ConormalAtlas.ofPresentation S)
              f σ q h) ≫
          Scheme.Hom.Conormal.map
            (ProjectiveBundle.SymmetricPresentation.ConormalAtlas.precompConormalSquare σ g) =
        ProjectiveBundle.SymmetricPresentation.ConormalAtlas.liftConormalPullbackComparison
            f g q ≫
          ProjectiveBundle.SymmetricPresentation.ConormalAtlas.liftConormalMap S
            (ProjectiveBundle.SymmetricPresentation.ConormalAtlas.ofPresentation S)
            (g ≫ f) (σ.precomp g)
            (ProjectiveBundle.SymmetricPresentation.ConormalAtlas.pullbackRepresentative f g q)
            (ProjectiveBundle.SymmetricPresentation.ConormalAtlas.pullbackRepresentative_class
              S f σ g q h))

end AlgebraicGeometry.Scheme
