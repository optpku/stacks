/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialRescale.Homology
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.GradedPieces

/-!
# Homology of the Standard Filtration Graded Pieces

This file passes the complex-level graded-piece comparisons for the two standard filtrations to
homology.  The first comparison includes the normalization which removes the total-complex sign
from representatives; the second comparison is induced directly by the flipped-row isomorphism.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]

/-- The self-inverse sign correction which turns the degreewise rescaling comparison into the
representative-preserving identification used on the first page. -/
noncomputable def First.GradedPiece.Homology.normalizationIso (p q : ℤ) :
    (K.X p).homology q ≅ (K.X p).homology q :=
  (p * q).negOnePow • Iso.refl _

/-- Homology of the reindexed first graded-piece complex is the vertical homology of the
corresponding column, under explicit column comparison data.  The intermediate differential
rescaling records the total-complex sign; the final self-inverse scalar normalizes the comparison
to preserve homology representatives. -/
@[stacks 0130 "first filtered graded-piece homology"]
noncomputable def First.GradedPiece.Homology.isoOf (p q : ℤ)
    (h : First.GradedPiece.ColumnComparison K p) :
    (FilteredComplex.GradedPiece.Column.complex (First.Filtration.total K) p).homology q ≅
      (K.X p).homology q :=
  HomologicalComplex.homologyMapIso (First.GradedPiece.columnIsoOf K p h) q ≪≫
    CochainComplex.rescaleDifferential.homologyIso (K.X p) p.negOnePow q ≪≫
    First.GradedPiece.Homology.normalizationIso K p q

/-- The forward first graded-piece homology comparison is the composite of the map induced by the
specified complex isomorphism and the canonical removal of differential rescaling. -/
theorem First.GradedPiece.Homology.isoOf_hom (p q : ℤ)
    (h : First.GradedPiece.ColumnComparison K p) :
    (First.GradedPiece.Homology.isoOf K p q h).hom =
      HomologicalComplex.homologyMap (First.GradedPiece.columnIsoOf K p h).hom q ≫
        (CochainComplex.rescaleDifferential.homologyIso
          (K.X p) p.negOnePow q).hom ≫
        (First.GradedPiece.Homology.normalizationIso K p q).hom := sorry

/-- Homology of the reindexed second graded-piece complex is the horizontal homology represented
by the corresponding column of the flipped double complex, under explicit row comparison data. -/
@[stacks 0130 "second filtered graded-piece homology"]
noncomputable def Second.GradedPiece.Homology.isoOf (p q : ℤ)
    (h : Second.GradedPiece.RowComparison K p) :
    (FilteredComplex.GradedPiece.Column.complex (Second.Filtration.total K) p).homology q ≅
      (K.flip.X p).homology q :=
  HomologicalComplex.homologyMapIso (Second.GradedPiece.rowIsoOf K p h) q

/-- The forward second graded-piece homology comparison is induced by the specified flipped-row
complex isomorphism. -/
theorem Second.GradedPiece.Homology.isoOf_hom (p q : ℤ)
    (h : Second.GradedPiece.RowComparison K p) :
    (Second.GradedPiece.Homology.isoOf K p q h).hom =
      HomologicalComplex.homologyMap (Second.GradedPiece.rowIsoOf K p h).hom q := sorry

end HomologicalComplex₂
