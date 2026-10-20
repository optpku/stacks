/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.PageOne
import StacksCheckRecall

/-!
# The First Differential of a Filtered-Complex Spectral Sequence

The reusable two-step quotient, boundary-map page, and filtration-raising API are owned by
`ReasLib.CategoryTheory.Filtration.Complex.PageOne`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
variable (A : FilteredComplex.Association K E) (hK hK' : K.RaisesFiltration)
variable (p q n n' : ℤ)

#check FilteredObject.Hom.RaisesFiltrationBy

#check FilteredComplex.Differential.RaisesFiltrationBy

#check HomologicalComplex.Filtered.TwoStep.shortExact

#check FilteredComplex.Page.One.complex

/- Lemma 12.24.3 (1) (012N): for an associated spectral sequence, `d₁` is the boundary map
of the canonical two-step quotient sequence. -/
@[stacks 012N "the first differential is the boundary map"]
#check (FilteredComplex.Page.One.d_eq_boundary A p q :
  CommSq
    ((E.page 1).d (p, q) (p + 1, q))
    ((A.pageOneIso p q).hom)
    ((A.pageOneIso (p + 1) q).hom)
    (FilteredComplex.Page.One.Boundary.bidegree K p q))

#check (FilteredComplex.Page.One.associatedIso A :
  E.page 1 ≅ FilteredComplex.Page.One.complex K)

/- Lemma 12.24.3 (2) (012N): a differential which raises the filtration induces zero
differentials on all graded-piece complexes. -/
@[stacks 012N "the differential on every graded piece is zero"]
#check (FilteredComplex.RaisesFiltration.gradedPiece_d_eq_zero hK n n' p :
  (K.gradedPiece p).d n n' = 0)

#check (FilteredComplex.RaisesFiltration.bidegreeMap_proof_irrel hK hK' p q :
  hK.bidegreeMap p q = hK'.bidegreeMap p q)

/- Lemma 12.24.3 (3) (012N): in the filtration-raising case, first-page cohomology is the
underlying graded-piece object. -/
@[stacks 012N "the first page for a filtration-raising differential"]
#check (FilteredComplex.RaisesFiltration.Page.One.homologyIso hK p q :
  (K.gradedPiece p).homology (p + q) ≅ (K.gradedPiece p).X (p + q))

/- Lemma 12.24.3 (4) (012N): after this identification, `d₁` is the map on graded pieces
induced by the original differential. -/
@[stacks 012N "the first differential when the filtration is raised"]
#check (FilteredComplex.Page.One.d_eq_raisedGradedPieceMap A hK p q :
  CommSq
    ((E.page 1).d (p, q) (p + 1, q))
    ((FilteredComplex.RaisesFiltration.Page.One.associatedIso hK A p q).hom)
    ((FilteredComplex.RaisesFiltration.Page.One.associatedIso hK A (p + 1) q).hom)
    (hK.bidegreeMap p q))
