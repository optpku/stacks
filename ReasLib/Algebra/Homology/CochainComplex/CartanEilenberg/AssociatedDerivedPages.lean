/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.DerivedPageNaturality
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.InitialPages

/-!
# Associated derived-functor pages of Cartan--Eilenberg resolutions

This file composes the initial-page comparisons for the standard filtrations of a double complex
with the Cartan--Eilenberg derived-functor comparisons.  Association with a spectral sequence is
kept as an explicit argument, while the resulting objectwise comparisons, differential squares,
and fixed-row complex comparison are exposed directly for downstream applications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K : CochainComplex.Plus A}

section FirstFiltration

variable (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
variable [(I.mapBicomplex F).HasTotal (up ℤ)]

namespace First.Association

/-- Lemma 13.21.4 (`015J`): specified association data for the first filtration identifies its
first page with the right derived functors of the terms of the source complex. -/
@[stacks 015J "the specified associated first-page right-derived identification"]
noncomputable def pageOneIso
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    (E.page 1).X (p, Int.ofNat q) ≅ (F.rightDerived q).obj (K.obj.X p) :=
  HomologicalComplex₂.First.Association.pageOneIso A h p (Int.ofNat q) ≪≫
    First.PageOne.rightDerivedIso I F p q

/-- The forward specified-association comparison factors through the generic first-page
comparison and the Cartan--Eilenberg right-derived comparison. -/
@[simp]
theorem pageOneIso_hom
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    (pageOneIso I F A h p q).hom =
      (HomologicalComplex₂.First.Association.pageOneIso
        A h p (Int.ofNat q)).hom ≫
        (First.PageOne.rightDerivedIso I F p q).hom := sorry

/-- The inverse specified-association comparison uses the inverse Cartan--Eilenberg
right-derived comparison followed by the inverse generic first-page comparison. -/
@[simp]
theorem pageOneIso_inv
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    (pageOneIso I F A h p q).inv =
      (First.PageOne.rightDerivedIso I F p q).inv ≫
        (HomologicalComplex₂.First.Association.pageOneIso
          A h p (Int.ofNat q)).inv := sorry

/-- The specified first-page comparisons intertwine the page differential and the map of right
derived functors induced by the source differential. -/
theorem pageOneIso_commSq
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    CommSq
      (f := (E.page 1).d (p, Int.ofNat q) (p + 1, Int.ofNat q))
      (g := (pageOneIso I F A h p q).hom)
      (h := (pageOneIso I F A h (p + 1) q).hom)
      (i := (F.rightDerived q).map (K.obj.d p (p + 1))) := sorry

/-- Conjugating the derived differential by the specified first-page comparison recovers the
page differential. -/
@[reassoc, stacks 015J "source differential computation for specified first-page comparisons"]
theorem pageOneIso_source_d
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    (pageOneIso I F A h p q).hom ≫
        (F.rightDerived q).map (K.obj.d p (p + 1)) ≫
      (pageOneIso I F A h (p + 1) q).inv =
      (E.page 1).d (p, Int.ofNat q) (p + 1, Int.ofNat q) := sorry

/-- Conjugating the page differential by the inverse specified first-page comparison recovers the
derived differential. -/
@[reassoc, stacks 015J "target differential computation for specified first-page comparisons"]
theorem pageOneIso_target_d
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    (pageOneIso I F A h p q).inv ≫
        (E.page 1).d (p, Int.ofNat q) (p + 1, Int.ofNat q) ≫
      (pageOneIso I F A h (p + 1) q).hom =
      (F.rightDerived q).map (K.obj.d p (p + 1)) := sorry

/-- Lemma 13.21.4 (`015J`): a specified first-filtration association packages each derived
degree as a presentation of the corresponding first-page row. -/
@[stacks 015J "the specified associated first-page row presentation"]
noncomputable def pageOnePresentation
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (q : ℕ) :
    CohomologicalSpectralSequence.PageOneRow.Presentation E (Int.ofNat q)
      (((F.rightDerived q).mapHomologicalComplex (up ℤ)).obj K.obj) where
  entryIso p := pageOneIso I F A h p q
  comm p := pageOneIso_commSq I F A h p q

/-- Lemma 13.21.4 (`015J`): the fixed row of a specified associated first page is the source
cochain complex after applying the corresponding right derived functor termwise. -/
@[stacks 015J "the specified associated first-page right-derived row comparison"]
noncomputable def pageOneComplexIso
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (q : ℕ) :
    E.pageOneRow (Int.ofNat q) ≅
      ((F.rightDerived q).mapHomologicalComplex (up ℤ)).obj K.obj :=
  CohomologicalSpectralSequence.PageOneRow.Presentation.complexIso
    (pageOnePresentation I F A h q)

/-- The forward component of the specified first-page row comparison is its objectwise
right-derived comparison. -/
@[simp]
theorem pageOneComplexIso_hom_f
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    (pageOneComplexIso I F A h q).hom.f p = (pageOneIso I F A h p q).hom := sorry

/-- The inverse component of the specified first-page row comparison is the inverse objectwise
right-derived comparison. -/
@[simp]
theorem pageOneComplexIso_inv_f
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    (pageOneComplexIso I F A h q).inv.f p = (pageOneIso I F A h p q).inv := sorry

/-- Lemma 13.21.4 (`015J`): specified first-filtration association data identifies the second
page with the homology of the termwise right-derived source complex. -/
@[stacks 015J "the specified associated first-page-two right-derived comparison"]
noncomputable def pageTwoIso
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    (E.page 2).X (p, Int.ofNat q) ≅
      (((F.rightDerived q).mapHomologicalComplex (up ℤ)).obj K.obj).homology p :=
  CohomologicalSpectralSequence.PageOneRow.Presentation.pageTwoIso
    (pageOnePresentation I F A h q) p

/-- The forward specified-association page-two comparison factors through the generic first
filtration comparison and the Cartan--Eilenberg right-derived homology comparison. -/
@[simp]
theorem pageTwoIso_hom
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    (pageTwoIso I F A h p q).hom =
      (HomologicalComplex₂.First.Association.pageTwoIso
        A h p (Int.ofNat q)).hom ≫
        (First.PageTwo.rightDerivedHomologyIso I F p q).hom := sorry

/-- The inverse specified-association page-two comparison first uses the inverse
Cartan--Eilenberg right-derived homology comparison and then the inverse generic first
filtration comparison. -/
@[simp]
theorem pageTwoIso_inv
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℤ) (q : ℕ) :
    (pageTwoIso I F A h p q).inv =
      (First.PageTwo.rightDerivedHomologyIso I F p q).inv ≫
        (HomologicalComplex₂.First.Association.pageTwoIso
          A h p (Int.ofNat q)).inv := sorry

end First.Association

end FirstFiltration

section SecondFiltration

variable (I : CartanEilenbergResolution K) (F : A ⥤ B)
variable [F.Additive] [PreservesFiniteLimits F]
variable [(I.mapBicomplex F).HasTotal (up ℤ)]

namespace Second.Association

/-- Lemma 13.21.4 (`015J`): specified association data for the second filtration identifies its
second page with the right derived functors of the homology objects of the source complex. -/
@[stacks 015J "the specified associated second-page right-derived identification"]
noncomputable def pageTwoIso
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.Second.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℕ) (q : ℤ) :
    (E.page 2).X (Int.ofNat p, q) ≅
      (F.rightDerived p).obj (K.obj.homology q) :=
  HomologicalComplex₂.Second.Association.pageTwoIso A h (Int.ofNat p) q ≪≫
    Second.PageTwo.rightDerivedIso I F p q

/-- The forward specified-association second-page comparison factors through the generic
second-filtration comparison and the Cartan--Eilenberg right-derived comparison. -/
@[simp]
theorem pageTwoIso_hom
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.Second.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℕ) (q : ℤ) :
    (pageTwoIso I F A h p q).hom =
      (HomologicalComplex₂.Second.Association.pageTwoIso
        A h (Int.ofNat p) q).hom ≫
        (Second.PageTwo.rightDerivedIso I F p q).hom := sorry

/-- The inverse specified-association second-page comparison uses the inverse Cartan--Eilenberg
right-derived comparison followed by the inverse generic second-filtration comparison. -/
@[simp]
theorem pageTwoIso_inv
    {E : CohomologicalSpectralSequence B 0}
    (A : FilteredComplex.Association
      (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex F)) E)
    (h : HomologicalComplex₂.Second.GradedPiece.Comparisons (I.mapBicomplex F))
    (p : ℕ) (q : ℤ) :
    (pageTwoIso I F A h p q).inv =
      (Second.PageTwo.rightDerivedIso I F p q).inv ≫
        (HomologicalComplex₂.Second.Association.pageTwoIso
          A h (Int.ofNat p) q).inv := sorry

end Second.Association

end SecondFiltration

end CochainComplex.CartanEilenbergResolution
