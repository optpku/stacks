/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.SpectralSequence
public import ReasLib.CategoryTheory.Sites.Grothendieck.SpectralSequence

/-!
# Lemma 85.8.3

In Situation 85.3.3, for `K` in `D⁺(C_total)` there is a cohomological spectral
sequence `(E_r, d_r)_{r ≥ 0}` with `E₁^{p,q} = H^q(C_p, K_p)` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`, converging to `H^{p+q}(C_total, K)`.
The spectral sequence is functorial in `K`.
-/

@[expose] public section

open CategoryTheory HomologicalComplex ComplexShape DerivedCategory Opposite
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

variable [EnoughInjectives (Sheaf (topology C J) AddCommGrpCat.{w})]

/- Lemma 85.8.3: existence and first-page differential on a morphism diagram of sites. -/
@[stacks 09WJ] #check (CategoryTheory.SimplicialSites.exists_spectralSequence C J :
  ∀ (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})),
    ∃ (S : WithAbutment (fun n ↦ abutmentFunctor C J n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅ (pageOneFunctor C J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (pageOneDifferential C J p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom)

/- Lemma 85.8.3: coherent functoriality on a morphism diagram of sites. -/
@[stacks 09WJ] #check (CategoryTheory.SimplicialSites.spectralSequence_functorial C J :
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
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n : ℕ,
    (fiberSectionsStageGamma F J n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}))]
variable [(fiberSectionsTotalFunctor F J).Additive]
variable [(fiberSectionsTotalFunctor F J).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}))]

variable [EnoughInjectives (Sheaf (topology F J) AddCommGrpCat.{w})]

/- Lemma 85.8.3: existence and first-page differential on a fiberwise simplicial site. -/
@[stacks 09WJ] #check (CategoryTheory.Grothendieck.exists_spectralSequence F J :
  ∀ (K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})),
    ∃ (S : WithAbutment (fun n ↦ fiberAbutmentFunctor F J n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (fiberPageOneFunctor F J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (fiberPageOneDifferential F J p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom)

/- Lemma 85.8.3: coherent functoriality on a fiberwise simplicial site. -/
@[stacks 09WJ] #check (CategoryTheory.Grothendieck.spectralSequence_functorial F J :
  ∃ (S : ∀ K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}),
        WithAbutment (fun n ↦ fiberAbutmentFunctor F J n) K)
      (pageOneIso : ∀ (K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})) (p q : ℤ),
        ((S K).sequence.page 1).X (p, q) ≅ (fiberPageOneFunctor F J p q).obj K)
      (m : ∀ {K L : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})} (f : K ⟶ L),
        WithAbutment.Map (fun n ↦ fiberAbutmentFunctor F J n) f (S K) (S L)),
      (∀ (K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})) (p q : ℤ),
        (pageOneIso K p q).hom ≫ (fiberPageOneDifferential F J p q).app K =
          ((S K).sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso K (p + 1) q).hom) ∧
      (∀ {K L : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})} (f : K ⟶ L) (p q : ℤ),
        ((m f).sequenceMap.hom 1).f (p, q) ≫ (pageOneIso L p q).hom =
          (pageOneIso K p q).hom ≫ (fiberPageOneFunctor F J p q).map f) ∧
      (∀ K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}),
        (m (𝟙 K)).sequenceMap = 𝟙 (S K).sequence) ∧
      (∀ {K L M : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})} (f : K ⟶ L) (g : L ⟶ M),
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap))

end CategoryTheory.Grothendieck
