/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialRescale.Functor
public import ReasLib.CategoryTheory.Filtration.Complex.GradedPieceColumn
public import ReasLib.CategoryTheory.Filtration.GradedPiece.Comparison
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Total.Projection

/-!
# Graded Pieces of the Standard Filtrations on a Double Complex

The associated graded complexes of the two standard filtrations on a total complex are identified
with a single column or row of the original double complex. The ambient filtered-object API owns
the cokernel universal property. This module constructs the stage projections and quotient maps
and supplies their comparison laws for every double complex with a total complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u v

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]

/-! ## First filtration -/

/-- Projection from the `p`-th stage of the first filtration in total degree `p + q` to the
surviving `(p,q)` summand. -/
@[stacks 0130 "first graded-piece stage projection"]
noncomputable def First.GradedPiece.stageProjection (p q : ℤ) :
    ((First.Filtration.object K) (p + q)).stage p ⟶ (K.X p).X q :=
  (((First.Filtration.object K) (p + q)).filtration.stage p).arrow ≫
    Total.πTotal K p q (p + q)

/-- The first-filtration projection kills the next filtration stage.  This is a source-facing
proposition; quotient maps use an explicit proof of the same condition. -/
@[stacks 0130 "first graded-piece projection vanishing"]
theorem First.GradedPiece.succ_comp_stageProjection (p q : ℤ) :
    ((First.Filtration.object K) (p + q)).succInclusion p ≫
        First.GradedPiece.stageProjection K p q = 0 := sorry

/-- The cokernel descent from a first graded-piece component to the corresponding column entry,
formed from an explicit vanishing proof. -/
@[stacks 0130 "first graded-piece component descent"]
noncomputable def First.GradedPiece.componentHomOf (p q : ℤ)
    (h_zero : ((First.Filtration.object K) (p + q)).succInclusion p ≫
      First.GradedPiece.stageProjection K p q = 0) :
    ((First.Filtration.object K) (p + q)).gradedPiece p ⟶ (K.X p).X q :=
  FilteredObject.GradedPiece.desc ((First.Filtration.object K) (p + q)) p
    (First.GradedPiece.stageProjection K p q) h_zero

/-- The canonical map from a first-filtration column entry to its graded-piece quotient. -/
@[stacks 0130 "first graded-piece quotient inclusion"]
noncomputable def First.GradedPiece.componentToQuotient (p q : ℤ) :
    (K.X p).X q ⟶ ((First.Filtration.object K) (p + q)).gradedPiece p :=
  K.ιTotal (up ℤ) p q (p + q) rfl ≫
    factorThruImageSubobject ((First.Filtration.cutoff K) (p + q) p) ≫
    cokernel.π (((First.Filtration.object K) (p + q)).succInclusion p)

/-- The proposition-level data identifying one first graded-piece component with its column
entry after a specified quotient descent. -/
@[stacks 0130 "first graded-piece component comparison"]
abbrev First.GradedPiece.ComponentComparison (p q : ℤ)
    (h_zero : ((First.Filtration.object K) (p + q)).succInclusion p ≫
      First.GradedPiece.stageProjection K p q = 0) : Prop :=
  FilteredObject.GradedPiece.Comparison
    ((First.Filtration.object K) (p + q)) p
    (First.GradedPiece.stageProjection K p q)
    (First.GradedPiece.componentHomOf K p q h_zero)
    (First.GradedPiece.componentToQuotient K p q)

/-- The component isomorphism induced by explicit first-filtration comparison laws. -/
@[stacks 0130 "first graded-piece component isomorphism"]
noncomputable def First.GradedPiece.componentIsoOf (p q : ℤ)
    (h_zero : ((First.Filtration.object K) (p + q)).succInclusion p ≫
      First.GradedPiece.stageProjection K p q = 0)
    (h : First.GradedPiece.ComponentComparison K p q h_zero) :
    ((First.Filtration.object K) (p + q)).gradedPiece p ≅ (K.X p).X q :=
  FilteredObject.GradedPiece.Comparison.isoOf h

/-- Coherent componentwise comparison data from a first graded-piece column to the corresponding
signed vertical column. -/
@[stacks 0130 "first graded-piece column comparison"]
structure First.GradedPiece.ColumnComparison (p : ℤ) : Prop where
  /-- Each stage projection kills the next filtration stage. -/
  h_zero : ∀ q : ℤ, ((First.Filtration.object K) (p + q)).succInclusion p ≫
    First.GradedPiece.stageProjection K p q = 0
  /-- Each quotient descent and inclusion are mutually inverse. -/
  component : ∀ q : ℤ, First.GradedPiece.ComponentComparison K p q (h_zero q)
  /-- The quotient descents commute with the signed vertical differentials. -/
  comm : ∀ i j : ℤ, (up ℤ).Rel i j →
    First.GradedPiece.componentHomOf K p i (h_zero i) ≫
        (CochainComplex.rescaleDifferential (K.X p) (p.negOnePow : ℤ)).d i j =
      (FilteredComplex.GradedPiece.Column.complex (First.Filtration.total K) p).d i j ≫
        First.GradedPiece.componentHomOf K p j (h_zero j)

/-- Coherent first-filtration graded-piece comparisons in every filtration degree. -/
@[stacks 0130 "first graded-piece comparisons"]
abbrev First.GradedPiece.Comparisons : Prop :=
  ∀ p : ℤ, First.GradedPiece.ColumnComparison K p

/-- The canonical quotient descents and inclusions identify every first graded-piece column
with the signed vertical column, for any double complex admitting a total complex. -/
@[stacks 0130 "canonical first graded-piece comparison laws"]
theorem First.GradedPiece.comparisons : First.GradedPiece.Comparisons K := by
  intro p
  refine
    { h_zero := First.GradedPiece.succ_comp_stageProjection K p
      component := ?_
      comm := ?_ }
  · intro q
    sorry
  · intro i j hij
    sorry

/-- The first reindexed graded-piece column isomorphism supplied by explicit componentwise
comparison data. -/
@[stacks 0130 "first graded-piece column isomorphism"]
noncomputable def First.GradedPiece.columnIsoOf (p : ℤ)
    (h : First.GradedPiece.ColumnComparison K p) :
    FilteredComplex.GradedPiece.Column.complex (First.Filtration.total K) p ≅
      CochainComplex.rescaleDifferential (K.X p) (p.negOnePow : ℤ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ First.GradedPiece.componentIsoOf K p q (h.h_zero q) (h.component q))
    h.comm

/-- The forward component of `columnIsoOf` is the supplied quotient descent. -/
@[stacks 0130 "first graded-piece column forward component"]
theorem First.GradedPiece.columnIsoOf_hom_f (p q : ℤ)
    (h : First.GradedPiece.ColumnComparison K p) :
    (First.GradedPiece.columnIsoOf K p h).hom.f q =
      First.GradedPiece.componentHomOf K p q (h.h_zero q) := sorry

/-- The inverse component of `columnIsoOf` is the canonical map into the graded-piece quotient. -/
@[stacks 0130 "first graded-piece column inverse component"]
theorem First.GradedPiece.columnIsoOf_inv_f (p q : ℤ)
    (h : First.GradedPiece.ColumnComparison K p) :
    (First.GradedPiece.columnIsoOf K p h).inv.f q =
      First.GradedPiece.componentToQuotient K p q := sorry

/-! ## Second filtration -/

/-- Projection from the `p`-th stage of the second filtration in total degree `p + q` to the
surviving `(q,p)` summand. -/
@[stacks 0130 "second graded-piece stage projection"]
noncomputable def Second.GradedPiece.stageProjection (p q : ℤ) :
    ((Second.Filtration.object K) (p + q)).stage p ⟶ (K.flip.X p).X q :=
  (((Second.Filtration.object K) (p + q)).filtration.stage p).arrow ≫
    Total.πTotal K q p (p + q)

/-- The second-filtration projection kills the next filtration stage.  This is a source-facing
proposition; quotient maps use an explicit proof of the same condition. -/
@[stacks 0130 "second graded-piece projection vanishing"]
theorem Second.GradedPiece.succ_comp_stageProjection (p q : ℤ) :
    ((Second.Filtration.object K) (p + q)).succInclusion p ≫
        Second.GradedPiece.stageProjection K p q = 0 := sorry

/-- The cokernel descent from a second graded-piece component to the corresponding flipped-row
entry, formed from an explicit vanishing proof. -/
@[stacks 0130 "second graded-piece component descent"]
noncomputable def Second.GradedPiece.componentHomOf (p q : ℤ)
    (h_zero : ((Second.Filtration.object K) (p + q)).succInclusion p ≫
      Second.GradedPiece.stageProjection K p q = 0) :
    ((Second.Filtration.object K) (p + q)).gradedPiece p ⟶ (K.flip.X p).X q :=
  FilteredObject.GradedPiece.desc ((Second.Filtration.object K) (p + q)) p
    (Second.GradedPiece.stageProjection K p q) h_zero

/-- The canonical map from a second-filtration flipped-row entry to its graded-piece quotient. -/
@[stacks 0130 "second graded-piece quotient inclusion"]
noncomputable def Second.GradedPiece.componentToQuotient (p q : ℤ) :
    (K.flip.X p).X q ⟶ ((Second.Filtration.object K) (p + q)).gradedPiece p :=
  K.ιTotal (up ℤ) q p (p + q) (rfl.trans (add_comm q p)) ≫
    factorThruImageSubobject ((Second.Filtration.cutoff K) (p + q) p) ≫
    cokernel.π (((Second.Filtration.object K) (p + q)).succInclusion p)

/-- The proposition-level data identifying one second graded-piece component with its flipped-row
entry after a specified quotient descent. -/
@[stacks 0130 "second graded-piece component comparison"]
abbrev Second.GradedPiece.ComponentComparison (p q : ℤ)
    (h_zero : ((Second.Filtration.object K) (p + q)).succInclusion p ≫
      Second.GradedPiece.stageProjection K p q = 0) : Prop :=
  FilteredObject.GradedPiece.Comparison
    ((Second.Filtration.object K) (p + q)) p
    (Second.GradedPiece.stageProjection K p q)
    (Second.GradedPiece.componentHomOf K p q h_zero)
    (Second.GradedPiece.componentToQuotient K p q)

/-- The component isomorphism induced by explicit second-filtration comparison laws. -/
@[stacks 0130 "second graded-piece component isomorphism"]
noncomputable def Second.GradedPiece.componentIsoOf (p q : ℤ)
    (h_zero : ((Second.Filtration.object K) (p + q)).succInclusion p ≫
      Second.GradedPiece.stageProjection K p q = 0)
    (h : Second.GradedPiece.ComponentComparison K p q h_zero) :
    ((Second.Filtration.object K) (p + q)).gradedPiece p ≅ (K.flip.X p).X q :=
  FilteredObject.GradedPiece.Comparison.isoOf h

/-- Coherent componentwise comparison data from a second graded-piece column to the corresponding
flipped row. -/
@[stacks 0130 "second graded-piece row comparison"]
structure Second.GradedPiece.RowComparison (p : ℤ) : Prop where
  /-- Each stage projection kills the next filtration stage. -/
  h_zero : ∀ q : ℤ, ((Second.Filtration.object K) (p + q)).succInclusion p ≫
    Second.GradedPiece.stageProjection K p q = 0
  /-- Each quotient descent and inclusion are mutually inverse. -/
  component : ∀ q : ℤ, Second.GradedPiece.ComponentComparison K p q (h_zero q)
  /-- The quotient descents commute with the horizontal differentials of the flipped row. -/
  comm : ∀ i j : ℤ, (up ℤ).Rel i j →
    Second.GradedPiece.componentHomOf K p i (h_zero i) ≫ (K.flip.X p).d i j =
      (FilteredComplex.GradedPiece.Column.complex (Second.Filtration.total K) p).d i j ≫
        Second.GradedPiece.componentHomOf K p j (h_zero j)

/-- Coherent second-filtration graded-piece comparisons in every filtration degree. -/
@[stacks 0130 "second graded-piece comparisons"]
abbrev Second.GradedPiece.Comparisons : Prop :=
  ∀ p : ℤ, Second.GradedPiece.RowComparison K p

/-- The canonical quotient descents and inclusions identify every second graded-piece column
with the unsigned flipped row, for any double complex admitting a total complex. -/
@[stacks 0130 "canonical second graded-piece comparison laws"]
theorem Second.GradedPiece.comparisons : Second.GradedPiece.Comparisons K := by
  intro p
  refine
    { h_zero := Second.GradedPiece.succ_comp_stageProjection K p
      component := ?_
      comm := ?_ }
  · intro q
    sorry
  · intro i j hij
    sorry

/-- The second reindexed graded-piece column isomorphism supplied by explicit componentwise
comparison data. -/
@[stacks 0130 "second graded-piece row isomorphism"]
noncomputable def Second.GradedPiece.rowIsoOf (p : ℤ)
    (h : Second.GradedPiece.RowComparison K p) :
    FilteredComplex.GradedPiece.Column.complex (Second.Filtration.total K) p ≅ K.flip.X p :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ Second.GradedPiece.componentIsoOf K p q (h.h_zero q) (h.component q))
    h.comm

/-- The forward component of `rowIsoOf` is the supplied quotient descent. -/
@[stacks 0130 "second graded-piece row forward component"]
theorem Second.GradedPiece.rowIsoOf_hom_f (p q : ℤ)
    (h : Second.GradedPiece.RowComparison K p) :
    (Second.GradedPiece.rowIsoOf K p h).hom.f q =
      Second.GradedPiece.componentHomOf K p q (h.h_zero q) := sorry

/-- The inverse component of `rowIsoOf` is the canonical map into the graded-piece quotient. -/
@[stacks 0130 "second graded-piece row inverse component"]
theorem Second.GradedPiece.rowIsoOf_inv_f (p q : ℤ)
    (h : Second.GradedPiece.RowComparison K p) :
    (Second.GradedPiece.rowIsoOf K p h).inv.f q =
      Second.GradedPiece.componentToQuotient K p q := sorry

end HomologicalComplex₂
