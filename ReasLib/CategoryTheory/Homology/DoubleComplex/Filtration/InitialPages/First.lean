module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.GradedPieceHomology
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageOneRow
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence

/-!
# Initial Pages for the First Standard Double-Complex Filtration

For a spectral sequence explicitly associated to the first standard filtration, this file
identifies the first page with vertical homology, assembles the objectwise comparison into an
isomorphism of fixed-row cochain complexes, and identifies the second page with horizontal
homology of that complex.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)} [K.HasTotal (up ℤ)]

/-- The first-page comparison obtained from specified association data for the first filtered
total. -/
@[stacks 0130 "first filtered spectral-sequence page one"]
noncomputable def First.Association.pageOneIso
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (p q : ℤ) :
    (E.page 1).X (p, q) ≅ (K.X p).homology q :=
  A.pageOneIso p q ≪≫
    (FilteredComplex.GradedPiece.Column.homologyIso (First.Filtration.total K) p q).symm ≪≫
    First.GradedPiece.Homology.isoOf K p q (h p)

/-- The forward comparison attached to specified association data factors through the canonical
page-one and graded-piece comparisons. -/
@[simp]
theorem First.Association.pageOneIso_hom
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (p q : ℤ) :
    (First.Association.pageOneIso A h p q).hom =
      (A.pageOneIso p q).hom ≫
        (FilteredComplex.GradedPiece.Column.homologyIso
          (First.Filtration.total K) p q).inv ≫
        (First.GradedPiece.Homology.isoOf K p q (h p)).hom := sorry

/-- The inverse comparison attached to specified association data factors through the inverse
graded-piece and page-one comparisons. -/
@[simp]
theorem First.Association.pageOneIso_inv
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (p q : ℤ) :
    (First.Association.pageOneIso A h p q).inv =
      (First.GradedPiece.Homology.isoOf K p q (h p)).inv ≫
        (FilteredComplex.GradedPiece.Column.homologyIso
          (First.Filtration.total K) p q).hom ≫
        (A.pageOneIso p q).inv := sorry

/-- The specified first-page comparisons intertwine the spectral-sequence differential with the
first filtered page-one differential. -/
theorem First.Association.pageOneIso_commSq
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (p q : ℤ) :
    CommSq
      ((E.page 1).d (p, q) (p + 1, q))
      (First.Association.pageOneIso A h p q).hom
      (First.Association.pageOneIso A h (p + 1) q).hom
      (First.PageOne.differential K p q) := sorry

/-- A specified first-page association assembles into a presentation of each fixed row. -/
@[stacks 0130 "first filtered page-one row presentation"]
noncomputable def First.Association.pageOnePresentation
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (q : ℤ) :
    CohomologicalSpectralSequence.PageOneRow.Presentation E q (First.PageOne.complex K q) where
  entryIso p := First.Association.pageOneIso A h p q
  comm p := First.Association.pageOneIso_commSq A h p q

/-- The fixed-row comparison obtained from specified association data. -/
@[stacks 0130 "first filtered page-one row"]
noncomputable def First.Association.pageOneComplexIso
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (q : ℤ) :
    E.pageOneRow q ≅ First.PageOne.complex K q :=
  CohomologicalSpectralSequence.PageOneRow.Presentation.complexIso
    (First.Association.pageOnePresentation A h q)

/-- The forward component of the specified fixed-row comparison is the objectwise comparison. -/
@[simp]
theorem First.Association.pageOneComplexIso_hom_f
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (p q : ℤ) :
    (First.Association.pageOneComplexIso A h q).hom.f p =
      (First.Association.pageOneIso A h p q).hom := sorry

/-- The inverse component of the specified fixed-row comparison is the inverse objectwise
comparison. -/
@[simp]
theorem First.Association.pageOneComplexIso_inv_f
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (p q : ℤ) :
    (First.Association.pageOneComplexIso A h q).inv.f p =
      (First.Association.pageOneIso A h p q).inv := sorry

/-- The page-two comparison obtained from specified association data for the first filtration. -/
@[stacks 0130 "first filtered page-two comparison"]
noncomputable def First.Association.pageTwoIso
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (p q : ℤ) :
    (E.page 2).X (p, q) ≅ First.PageTwo.entry K p q :=
  CohomologicalSpectralSequence.PageOneRow.Presentation.pageTwoIso
    (First.Association.pageOnePresentation A h q) p

/-- The forward specified-association page-two comparison is induced by the rowwise first-page
comparison. -/
theorem First.Association.pageTwoIso_hom
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (p q : ℤ) :
    (First.Association.pageTwoIso A h p q).hom =
      (E.iso 1 2 (p, q)).inv ≫
        (CohomologicalSpectralSequence.PageOneRow.homologyIso E p q).inv ≫
        HomologicalComplex.homologyMap (First.Association.pageOneComplexIso A h q).hom p := sorry

/-- The inverse specified-association page-two comparison is induced by the inverse rowwise
first-page comparison. -/
theorem First.Association.pageTwoIso_inv
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (First.Filtration.total K) E)
    (h : First.GradedPiece.Comparisons K) (p q : ℤ) :
    (First.Association.pageTwoIso A h p q).inv =
      HomologicalComplex.homologyMap (First.Association.pageOneComplexIso A h q).inv p ≫
        (CohomologicalSpectralSequence.PageOneRow.homologyIso E p q).hom ≫
        (E.iso 1 2 (p, q)).hom := sorry

end HomologicalComplex₂
