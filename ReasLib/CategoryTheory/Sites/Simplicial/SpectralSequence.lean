module

public import ReasLib.CategoryTheory.Sites.Simplicial.Bicomplex
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment

/-!
# Čech–injective double complex on a morphism diagram of sites

A cochain complex `I` of abelian sheaves on `C_total`
determines the double complex `A^{p,q} = Γ(C_p, I^q_p)` whose horizontal
differentials are those of `globalSectionsComplex` and whose vertical
differentials come from `I`. The associated first-page and abutment functors on
`DerivedCategory.Plus` recover `H^q(C_p, K_p)` and `H^n(C_total, K)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory ZeroObject
open scoped HomologicalComplex₂
open FilteredComplex.SpectralSequence.Realization

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]

variable [∀ n : ℕ,
    (sectionsStageGamma C J n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]
variable [(globalSectionsTotalFunctor C J).Additive]
variable [(globalSectionsTotalFunctor C J).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]

/-- Bounded-below derived abelian sheaves on a total simplicial site have a
convergent spectral sequence with stage cohomology on the first page and the
canonical alternating-coface differential. -/
theorem exists_spectralSequence
    [EnoughInjectives (Sheaf (topology C J) AddCommGrpCat.{w})]
    (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})) :
    ∃ (S : WithAbutment (fun n ↦ abutmentFunctor C J n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅ (pageOneFunctor C J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (pageOneDifferential C J p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- The stage-cohomology spectral sequences can be chosen simultaneously for all
bounded-below derived abelian sheaves, with natural first-page comparisons and
maps preserving identities and composition on spectral sequences. -/
theorem spectralSequence_functorial
    [EnoughInjectives (Sheaf (topology C J) AddCommGrpCat.{w})] :
    ∃ (S : ∀ K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}),
        WithAbutment (fun n ↦ abutmentFunctor C J n) K)
      (pageOneIso : ∀ (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})) (p q : ℤ),
        ((S K).sequence.page 1).X (p, q) ≅ (pageOneFunctor C J p q).obj K)
      (m : ∀ {K L : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})} (f : K ⟶ L),
        WithAbutment.Map (fun n ↦ abutmentFunctor C J n) f (S K) (S L)),
      (∀ (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})) (p q : ℤ),
        (pageOneIso K p q).hom ≫ (pageOneDifferential C J p q).app K =
          ((S K).sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso K (p + 1) q).hom) ∧
      (∀ {K L : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})} (f : K ⟶ L) (p q : ℤ),
        ((m f).sequenceMap.hom 1).f (p, q) ≫ (pageOneIso L p q).hom =
          (pageOneIso K p q).hom ≫ (pageOneFunctor C J p q).map f) ∧
      (∀ K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}),
        (m (𝟙 K)).sequenceMap = 𝟙 (S K).sequence) ∧
      (∀ {K L M : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})} (f : K ⟶ L) (g : L ⟶ M),
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap) :=
  sorry

end CategoryTheory.SimplicialSites
