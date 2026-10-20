module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.GradedPieceHomology
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageOneRow
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence

/-!
# Initial Pages for the Second Standard Double-Complex Filtration

For a spectral sequence explicitly associated to the second standard filtration, this file
identifies the first page with horizontal homology, assembles the objectwise comparison into a
signed fixed-row cochain-complex isomorphism, and identifies the second page with the homology of
that complex.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)} [K.HasTotal (up ℤ)]

/-- The first-page comparison obtained from specified association data for the second filtered
total. -/
@[stacks 0130 "second filtered spectral-sequence page one"]
noncomputable def Second.Association.pageOneIso
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (p q : ℤ) :
    (E.page 1).X (p, q) ≅ (K.flip.X p).homology q :=
  A.pageOneIso p q ≪≫
    (FilteredComplex.GradedPiece.Column.homologyIso (Second.Filtration.total K) p q).symm ≪≫
    Second.GradedPiece.Homology.isoOf K p q (h p)

/-- The forward comparison attached to specified association data factors through the canonical
page-one and graded-piece comparisons. -/
@[simp]
theorem Second.Association.pageOneIso_hom
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (p q : ℤ) :
    (Second.Association.pageOneIso A h p q).hom =
      (A.pageOneIso p q).hom ≫
        (FilteredComplex.GradedPiece.Column.homologyIso
          (Second.Filtration.total K) p q).inv ≫
        (Second.GradedPiece.Homology.isoOf K p q (h p)).hom := sorry

/-- The inverse comparison attached to specified association data factors through the inverse
graded-piece and page-one comparisons. -/
@[simp]
theorem Second.Association.pageOneIso_inv
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (p q : ℤ) :
    (Second.Association.pageOneIso A h p q).inv =
      (Second.GradedPiece.Homology.isoOf K p q (h p)).inv ≫
        (FilteredComplex.GradedPiece.Column.homologyIso
          (Second.Filtration.total K) p q).hom ≫
        (A.pageOneIso p q).inv := sorry

/-- The specified second-page comparisons intertwine the spectral-sequence differential with the
second filtered page-one differential. -/
theorem Second.Association.pageOneIso_commSq
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (p q : ℤ) :
    CommSq
      ((E.page 1).d (p, q) (p + 1, q))
      (Second.Association.pageOneIso A h p q).hom
      (Second.Association.pageOneIso A h (p + 1) q).hom
      (Second.PageOne.differential K p q) := sorry

/-- A specified second-page association assembles into a presentation of each fixed row. -/
@[stacks 0130 "second filtered page-one row presentation"]
noncomputable def Second.Association.pageOnePresentation
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (q : ℤ) :
    CohomologicalSpectralSequence.PageOneRow.Presentation E q (Second.PageOne.complex K q) where
  entryIso p := Second.Association.pageOneIso A h p q
  comm p := Second.Association.pageOneIso_commSq A h p q

/-- The fixed-row comparison obtained from specified association data. -/
@[stacks 0130 "second filtered page-one row"]
noncomputable def Second.Association.pageOneComplexIso
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (q : ℤ) :
    E.pageOneRow q ≅ Second.PageOne.complex K q :=
  CohomologicalSpectralSequence.PageOneRow.Presentation.complexIso
    (Second.Association.pageOnePresentation A h q)

/-- The forward component of the specified fixed-row comparison is the objectwise comparison. -/
@[simp]
theorem Second.Association.pageOneComplexIso_hom_f
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (p q : ℤ) :
    (Second.Association.pageOneComplexIso A h q).hom.f p =
      (Second.Association.pageOneIso A h p q).hom := sorry

/-- The inverse component of the specified fixed-row comparison is the inverse objectwise
comparison. -/
@[simp]
theorem Second.Association.pageOneComplexIso_inv_f
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (p q : ℤ) :
    (Second.Association.pageOneComplexIso A h q).inv.f p =
      (Second.Association.pageOneIso A h p q).inv := sorry

/-- The page-two comparison obtained from specified association data for the second filtration. -/
@[stacks 0130 "second filtered page-two comparison"]
noncomputable def Second.Association.pageTwoIso
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (p q : ℤ) :
    (E.page 2).X (p, q) ≅ Second.PageTwo.entry K p q :=
  CohomologicalSpectralSequence.PageOneRow.Presentation.pageTwoIso
    (Second.Association.pageOnePresentation A h q) p

/-- The forward specified-association page-two comparison is induced by the rowwise first-page
comparison. -/
theorem Second.Association.pageTwoIso_hom
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (p q : ℤ) :
    (Second.Association.pageTwoIso A h p q).hom =
      (E.iso 1 2 (p, q)).inv ≫
        (CohomologicalSpectralSequence.PageOneRow.homologyIso E p q).inv ≫
        HomologicalComplex.homologyMap (Second.Association.pageOneComplexIso A h q).hom p := sorry

/-- The inverse specified-association page-two comparison is induced by the inverse rowwise
first-page comparison. -/
theorem Second.Association.pageTwoIso_inv
    {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association (Second.Filtration.total K) E)
    (h : Second.GradedPiece.Comparisons K) (p q : ℤ) :
    (Second.Association.pageTwoIso A h p q).inv =
      HomologicalComplex.homologyMap (Second.Association.pageOneComplexIso A h q).inv p ≫
        (CohomologicalSpectralSequence.PageOneRow.homologyIso E p q).hom ≫
        (E.iso 1 2 (p, q)).hom := sorry

end HomologicalComplex₂
