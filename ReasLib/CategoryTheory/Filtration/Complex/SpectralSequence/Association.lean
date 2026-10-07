module

public import ReasLib.CategoryTheory.Filtration.Complex.GradedPieceColumn
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Presentation
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageZeroColumn

/-!
# Spectral Sequences Associated to Filtered Complexes

This file packages the zeroth-page comparison, the resulting first-page comparison, and the
association of a cohomological spectral sequence to a filtered complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- A chosen comparison between the zeroth page of a spectral sequence and the reindexed
graded-piece complexes of a filtered complex. Each column is a complex in its own right, so the
columnwise form avoids imposing an artificial definitional realization of the full zeroth page. -/
@[stacks 012M "zeroth-page comparison with graded pieces"]
structure Page.Zero.Comparison (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0) where
  /-- The comparison of the column at filtration degree `p`. -/
  columnIso : ∀ p : ℤ, E.pageZeroColumn p ≅ GradedPiece.Column.complex K p

/-- The representation-independent proposition that the zeroth page of `E` is the graded-piece
complex of `K`. -/
@[stacks 012M "zeroth page is the graded-piece complex"]
def Page.Zero.IsGradedPiece (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0) : Prop :=
  Nonempty (Page.Zero.Comparison K E)

/-- A chosen zeroth-page comparison witnesses the corresponding representation-independent
property. -/
@[stacks 012M "zeroth-page comparison witnesses the graded-piece property"]
theorem Page.Zero.Comparison.isGradedPiece
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Zero.Comparison K E) :
    Page.Zero.IsGradedPiece K E := sorry

/-- A zeroth-page comparison induces the usual identification of the first-page objects with
the cohomology of the graded-piece complexes. -/
@[stacks 012M "first-page comparison from a zeroth-page comparison"]
noncomputable def Page.One.iso
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Zero.Comparison K E) (p q : ℤ) :
    (E.page 1).X (p, q) ≅ (K.gradedPiece p).homology (p + q) :=
  (E.iso 0 1 (p, q)).symm ≪≫
    (CohomologicalSpectralSequence.PageZeroColumn.homologyIso E p q).symm ≪≫
    HomologicalComplex.homologyMapIso (A.columnIso p) q ≪≫
    GradedPiece.Column.homologyIso K p q

/-- A chosen association between a filtered complex and a cohomological spectral sequence. It
contains both the all-page representative presentation and the zeroth-page graded-piece
comparison required to form concrete initial-page identifications. -/
@[stacks 012M "spectral sequence associated to a filtered complex"]
structure Association (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0)
    extends Page.Presentation K E, Page.Zero.Comparison K E

/-- The canonical first-page comparison carried by an association. This is the convenient
downstream form of its zeroth-page graded-piece comparison. -/
@[stacks 012M "first-page comparison from an association"]
noncomputable def Association.pageOneIso
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Association K E) (p q : ℤ) :
    (E.page 1).X (p, q) ≅ (K.gradedPiece p).homology (p + q) :=
  Page.One.iso A.toComparison p q

/-- A selected cohomological spectral sequence together with concrete association data for a
fixed filtered complex. Unlike `IsAssociated`, this is data and can therefore be passed to
constructions that need to retain the chosen sequence and its page comparisons. -/
@[stacks 012M "chosen spectral sequence associated to a filtered complex"]
structure AssociatedSpectralSequence (K : FilteredComplex C) where
  /-- The selected cohomological spectral sequence. -/
  sequence : CohomologicalSpectralSequence C 0
  /-- Concrete association data for the selected spectral sequence. -/
  association : Association K sequence

/-- Bundle specified association data with the spectral sequence to which it applies. -/
@[stacks 012M "chosen spectral sequence associated to a filtered complex"]
def Association.toAssociatedSpectralSequence
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Association K E) : AssociatedSpectralSequence K where
  sequence := E
  association := A

end FilteredComplex

/-- Stacks 012M: a cohomological spectral sequence is associated to a filtered complex when all
its entries are the explicit subquotients `Zᵣ^{p,q}/Bᵣ^{p,q}`, its differentials admit the
strict-cycle quotient representation of the filtered-complex differential, and its zeroth page
is the associated graded complex. The last condition also supplies the canonical first-page
comparison with graded-piece cohomology. -/
@[stacks 012M "spectral sequence associated to a filtered complex"]
def FilteredComplex.IsAssociated (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0) : Prop :=
  Nonempty (FilteredComplex.Association K E)

namespace FilteredComplex

namespace AssociatedSpectralSequence

/-- The selected association data carried by an `AssociatedSpectralSequence` supplies the
corresponding representation-independent proposition. -/
@[stacks 012M "spectral sequence associated to a filtered complex"]
theorem isAssociated {K : FilteredComplex C} (S : AssociatedSpectralSequence K) :
    IsAssociated K S.sequence := sorry

end AssociatedSpectralSequence

/-- The association proposition implies the all-page representative property. -/
@[stacks 012M "association implies an all-page presentation"]
theorem IsAssociated.hasPresentation
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (h : IsAssociated K E) :
    Page.HasPresentation K E := sorry

/-- The association proposition implies the zeroth-page graded-piece property. -/
@[stacks 012M "association implies a graded zeroth page"]
theorem IsAssociated.isGradedPiece
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (h : IsAssociated K E) :
    Page.Zero.IsGradedPiece K E := sorry

/-- Every filtered complex admits a cohomological spectral sequence with the explicit `Zᵣ/Bᵣ`
pages, strict-cycle represented differentials, and canonical zeroth- and first-page comparisons. -/
@[stacks 012M "existence of an associated spectral sequence"]
theorem IsAssociated.exists (K : FilteredComplex C) :
    ∃ E : CohomologicalSpectralSequence C 0, IsAssociated K E := sorry

/-- Every filtered complex admits a selected cohomological spectral sequence together with
concrete association data. The result is `Nonempty` because the selection is not canonical. -/
@[stacks 012M "chosen spectral sequence associated to a filtered complex"]
theorem AssociatedSpectralSequence.nonempty (K : FilteredComplex C) :
    Nonempty (AssociatedSpectralSequence K) := sorry

end FilteredComplex

end CategoryTheory
