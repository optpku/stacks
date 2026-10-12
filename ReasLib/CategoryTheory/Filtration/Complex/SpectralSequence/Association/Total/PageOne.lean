/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association.Total
public import Mathlib.Tactic.CrossRefAttribute

/-!
# First-page functors for total associated spectral sequences

This leaf packages the generic first-page comparison at the neutral association level.  Bounded
realizations and derived applications can reuse it without inheriting unrelated convergence data.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.AssociatedSpectralSequence.Total

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Hom

/-- The first-page comparison is natural for a total associated-spectral-sequence map. -/
@[reassoc, stacks 012O "first-page naturality for a total associated spectral sequence"]
theorem pageOne_naturality {S T : Total (C := C)} (f : Hom S T) (p q : ℤ) :
    ((Hom.sequenceMap f).hom 1).f (p, q) ≫
        (T.association.pageOneIso p q).hom =
      (S.association.pageOneIso p q).hom ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap f.filteredMap p) (p + q) := sorry

/-- Inverse first-page naturality for a total associated-spectral-sequence map. -/
@[reassoc, stacks 012O "inverse first-page naturality for a total associated spectral sequence"]
theorem pageOne_inv_naturality {S T : Total (C := C)} (f : Hom S T) (p q : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap f.filteredMap p) (p + q) ≫
        (T.association.pageOneIso p q).inv =
      (S.association.pageOneIso p q).inv ≫
        ((Hom.sequenceMap f).hom 1).f (p, q) := sorry

/-- Conjugating the graded-piece homology map by the first-page comparison recovers the page map
of a total associated-spectral-sequence morphism. -/
@[reassoc, stacks 012O "first-page map computation for a total associated spectral sequence"]
theorem pageOne_naturality_inv {S T : Total (C := C)} (f : Hom S T) (p q : ℤ) :
    (S.association.pageOneIso p q).hom ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap f.filteredMap p) (p + q) ≫
        (T.association.pageOneIso p q).inv =
      ((Hom.sequenceMap f).hom 1).f (p, q) := sorry

end Hom

/-- The `(p, q)` entry on the first page, functorial in a total associated object. -/
@[stacks 012O "first-page source functor on total associated spectral sequences"]
noncomputable abbrev pageOneSource (p q : ℤ) :
    Total (C := C) ⥤ C :=
  forgetSequence ⋙
    CategoryTheory.SpectralSequence.pageFunctor C _ 0 1 ⋙
    HomologicalComplex.eval C _ (p, q)

/-- The `(p, q)` graded-piece homology target, functorial in a total associated object. -/
@[stacks 012O "first-page target functor on total associated spectral sequences"]
noncomputable abbrev pageOneTarget (p q : ℤ) :
    Total (C := C) ⥤ C :=
  forgetFiltered ⋙ FilteredComplex.gradedPieceFunctor p ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (p + q)

/-- The first-page comparison, natural in a total associated object. -/
@[stacks 012O "first-page comparison on total associated spectral sequences"]
noncomputable def pageOneComparison (p q : ℤ) :
    pageOneSource (C := C) p q ≅ pageOneTarget (C := C) p q :=
  NatIso.ofComponents (fun S ↦ S.association.pageOneIso p q)
    (fun f ↦ FilteredComplex.Association.Hom.pageOne_naturality f.associationMap p q)

/-- Evaluation of the source functor returns the selected page entry. -/
@[simp, stacks 012O "first-page source evaluation on total associated objects"]
theorem pageOneSource_obj (p q : ℤ) (S : Total (C := C)) :
    (pageOneSource (C := C) p q).obj S = (S.sequence.page 1).X (p, q) := sorry

/-- The source functor acts on a total map by its selected page component. -/
@[simp, stacks 012O "first-page source map on total associated objects"]
theorem pageOneSource_map (p q : ℤ) {S T : Total (C := C)} (f : S ⟶ T) :
    (pageOneSource (C := C) p q).map f =
      ((Hom.sequenceMap f).hom 1).f (p, q) := sorry

/-- Evaluation of the target functor returns graded-piece homology. -/
@[simp, stacks 012O "first-page target evaluation on total associated objects"]
theorem pageOneTarget_obj (p q : ℤ) (S : Total (C := C)) :
    (pageOneTarget (C := C) p q).obj S =
      (S.filtered.gradedPiece p).homology (p + q) := sorry

/-- The target functor acts by the induced graded-piece homology map. -/
@[simp, stacks 012O "first-page target map on total associated objects"]
theorem pageOneTarget_map (p q : ℤ) {S T : Total (C := C)} (f : S ⟶ T) :
    (pageOneTarget (C := C) p q).map f =
      HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap f.filteredMap p) (p + q) := sorry

/-- The component of the total first-page comparison is the stored association comparison. -/
@[simp, stacks 012O "component of the total first-page comparison"]
theorem pageOneComparison_app (p q : ℤ) (S : Total (C := C)) :
    (pageOneComparison (C := C) p q).app S = S.association.pageOneIso p q := sorry

/-- The forward component of the total first-page comparison. -/
@[simp, stacks 012O "forward component of the total first-page comparison"]
theorem pageOneComparison_hom_app (p q : ℤ) (S : Total (C := C)) :
    (pageOneComparison (C := C) p q).hom.app S =
      (S.association.pageOneIso p q).hom := sorry

/-- The inverse component of the total first-page comparison. -/
@[simp, stacks 012O "inverse component of the total first-page comparison"]
theorem pageOneComparison_inv_app (p q : ℤ) (S : Total (C := C)) :
    (pageOneComparison (C := C) p q).inv.app S =
      (S.association.pageOneIso p q).inv := sorry

/-- Naturality of the forward total first-page comparison. -/
@[reassoc, stacks 012O "naturality of the total first-page comparison"]
theorem pageOneComparison_hom_naturality (p q : ℤ)
    {S T : Total (C := C)} (f : S ⟶ T) :
    (pageOneSource (C := C) p q).map f ≫
        (pageOneComparison (C := C) p q).hom.app T =
      (pageOneComparison (C := C) p q).hom.app S ≫
        (pageOneTarget (C := C) p q).map f := sorry

/-- Naturality of the inverse total first-page comparison. -/
@[reassoc, stacks 012O "inverse naturality of the total first-page comparison"]
theorem pageOneComparison_inv_naturality (p q : ℤ)
    {S T : Total (C := C)} (f : S ⟶ T) :
    (pageOneTarget (C := C) p q).map f ≫
        (pageOneComparison (C := C) p q).inv.app T =
      (pageOneComparison (C := C) p q).inv.app S ≫
        (pageOneSource (C := C) p q).map f := sorry

/-- Compute a source first-page map by conjugating the target map with the comparison. -/
@[reassoc, stacks 012O "source-map computation for the total first-page comparison"]
theorem pageOneComparison_source_map (p q : ℤ)
    {S T : Total (C := C)} (f : S ⟶ T) :
    (pageOneComparison (C := C) p q).hom.app S ≫
        (pageOneTarget (C := C) p q).map f ≫
        (pageOneComparison (C := C) p q).inv.app T =
      (pageOneSource (C := C) p q).map f := sorry

/-- Compute a target first-page map by conjugating the source map with the inverse comparison. -/
@[reassoc, stacks 012O "target-map computation for the total first-page comparison"]
theorem pageOneComparison_target_map (p q : ℤ)
    {S T : Total (C := C)} (f : S ⟶ T) :
    (pageOneComparison (C := C) p q).inv.app S ≫
        (pageOneSource (C := C) p q).map f ≫
        (pageOneComparison (C := C) p q).hom.app T =
      (pageOneTarget (C := C) p q).map f := sorry

end CategoryTheory.FilteredComplex.AssociatedSpectralSequence.Total
