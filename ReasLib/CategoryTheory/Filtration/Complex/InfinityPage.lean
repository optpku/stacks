/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Cohomology
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded
public import ReasLib.CategoryTheory.Homology.SpectralSequence.LimitStages
public import ReasLib.CategoryTheory.Subobject.Quotient

/-!
# Infinity Pages of Filtered Complexes

Explicit limit stages on an associated spectral sequence determine its infinity page.  Each graded
piece of the induced cohomology filtration is a subquotient of the corresponding infinity-page
entry.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory
namespace FilteredComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Cohomology

namespace GradedPiece

/-- A graded piece of filtered-complex cohomology is a subquotient of the infinity-page entry
defined by explicit limit stages. -/
@[stacks 012Q "cohomology graded pieces as infinity-page subquotients"]
theorem isSubquotient_of_limitPage
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E))
    (n p : ℤ) :
    IsSubquotient ((K.inducedCohomologyFiltration n).gradedPiece p)
      (L.infinityPage (p, n - p)) := sorry

/-- A graded piece of filtered-complex cohomology is a subquotient of the textbook quotient
`Z∞ / B∞` attached to explicit limit stages. -/
@[stacks 012Q "cohomology graded pieces as textbook infinity-page subquotients"]
theorem isSubquotient_of_limitPageQuotient
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E))
    (n p : ℤ) :
    IsSubquotient ((K.inducedCohomologyFiltration n).gradedPiece p)
      (cokernel (Subobject.ofLE
        (L.boundary (p, n - p))
        (L.cycle (p, n - p))
        (L.boundary_le_cycle (p, n - p)))) := sorry

/-- With the canonical subobject-lattice limit stages, a graded piece of cohomology is a
subquotient of the canonical infinity page. -/
@[stacks 012Q "cohomology graded pieces as canonical infinity-page subquotients"]
theorem isSubquotient_of_infinityPage
    [LocallySmall.{v} C] [WellPowered.{v} C]
    [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E) (n p : ℤ) :
    IsSubquotient ((K.inducedCohomologyFiltration n).gradedPiece p)
      ((CohomologicalSpectralSequence.Page.One.ofZero E).infinityPage (p, n - p)) := sorry

end GradedPiece

end Cohomology

end FilteredComplex
end CategoryTheory
