/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Realization.ToTotal
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association.Total.PageOne
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Tactic.CrossRefAttribute

/-!
# First-page functors for filtered spectral-sequence realizations

This neutral leaf packages the generic first-page comparison carried by a realization.  Derived,
bounded, and abutment-specific applications can compose these functors instead of rebuilding the
same page-evaluation and graded-piece-homology square.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.SpectralSequence.Realization

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The `(p, q)` entry on the first page, functorial in a generic realization. -/
@[stacks 012O "first-page source functor on filtered spectral-sequence realizations"]
noncomputable abbrev pageOneSource (p q : ℤ) :
    Realization (C := C) ⥤ C :=
  totalFunctor ⋙
    FilteredComplex.AssociatedSpectralSequence.Total.pageOneSource p q

/-- The `(p, q)` graded-piece homology target, functorial in a generic realization. -/
@[stacks 012O "first-page target functor on filtered spectral-sequence realizations"]
noncomputable abbrev pageOneTarget (p q : ℤ) :
    Realization (C := C) ⥤ C :=
  totalFunctor ⋙
    FilteredComplex.AssociatedSpectralSequence.Total.pageOneTarget p q

/-- The first-page comparison, natural in a generic filtered spectral-sequence realization. -/
@[stacks 012O "first-page comparison on filtered spectral-sequence realizations"]
noncomputable def pageOneComparison (p q : ℤ) :
    pageOneSource (C := C) p q ≅ pageOneTarget (C := C) p q :=
  Functor.isoWhiskerLeft (totalFunctor (C := C))
    (FilteredComplex.AssociatedSpectralSequence.Total.pageOneComparison p q)

/-- Evaluation of the generic first-page source returns the selected page entry. -/
@[simp, stacks 012O "first-page source evaluation on filtered realizations"]
theorem pageOneSource_obj (p q : ℤ) (S : Realization (C := C)) :
    (pageOneSource (C := C) p q).obj S = (S.sequence.page 1).X (p, q) := sorry

/-- The generic first-page source acts on a realization map by the selected page component. -/
@[simp, stacks 012O "first-page source map on filtered realizations"]
theorem pageOneSource_map (p q : ℤ) {S T : Realization (C := C)} (f : S ⟶ T) :
    (pageOneSource (C := C) p q).map f = (f.sequenceMap.hom 1).f (p, q) := sorry

/-- Evaluation of the generic first-page target returns graded-piece homology. -/
@[simp, stacks 012O "first-page target evaluation on filtered realizations"]
theorem pageOneTarget_obj (p q : ℤ) (S : Realization (C := C)) :
    (pageOneTarget (C := C) p q).obj S =
      (S.filtered.gradedPiece p).homology (p + q) := sorry

/-- The generic first-page target acts by the induced graded-piece homology map. -/
@[simp, stacks 012O "first-page target map on filtered realizations"]
theorem pageOneTarget_map (p q : ℤ) {S T : Realization (C := C)} (f : S ⟶ T) :
    (pageOneTarget (C := C) p q).map f =
      HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap f.filteredMap p) (p + q) := sorry

/-- The component of the generic first-page comparison is the stored association comparison. -/
@[simp, stacks 012O "component of the generic first-page comparison"]
theorem pageOneComparison_app (p q : ℤ) (S : Realization (C := C)) :
    (pageOneComparison (C := C) p q).app S = S.association.pageOneIso p q := sorry

/-- The forward component of the generic first-page comparison. -/
@[simp, stacks 012O "forward component of the generic first-page comparison"]
theorem pageOneComparison_hom_app (p q : ℤ) (S : Realization (C := C)) :
    (pageOneComparison (C := C) p q).hom.app S =
      (S.association.pageOneIso p q).hom := sorry

/-- The inverse component of the generic first-page comparison. -/
@[simp, stacks 012O "inverse component of the generic first-page comparison"]
theorem pageOneComparison_inv_app (p q : ℤ) (S : Realization (C := C)) :
    (pageOneComparison (C := C) p q).inv.app S =
      (S.association.pageOneIso p q).inv := sorry

/-- Naturality of the forward generic first-page comparison. -/
@[reassoc, stacks 012O "naturality of the generic first-page comparison"]
theorem pageOneComparison_hom_naturality (p q : ℤ)
    {S T : Realization (C := C)} (f : S ⟶ T) :
    (pageOneSource (C := C) p q).map f ≫
        (pageOneComparison (C := C) p q).hom.app T =
      (pageOneComparison (C := C) p q).hom.app S ≫
        (pageOneTarget (C := C) p q).map f := sorry

/-- Naturality of the inverse generic first-page comparison. -/
@[reassoc, stacks 012O "inverse naturality of the generic first-page comparison"]
theorem pageOneComparison_inv_naturality (p q : ℤ)
    {S T : Realization (C := C)} (f : S ⟶ T) :
    (pageOneTarget (C := C) p q).map f ≫
        (pageOneComparison (C := C) p q).inv.app T =
      (pageOneComparison (C := C) p q).inv.app S ≫
        (pageOneSource (C := C) p q).map f := sorry

/-- Compute a first-page source map by conjugating the target map with the comparison. -/
@[reassoc, stacks 012O "source-map computation through the generic first-page comparison"]
theorem pageOneComparison_source_map (p q : ℤ)
    {S T : Realization (C := C)} (f : S ⟶ T) :
    (pageOneComparison (C := C) p q).hom.app S ≫
        (pageOneTarget (C := C) p q).map f ≫
        (pageOneComparison (C := C) p q).inv.app T =
      (pageOneSource (C := C) p q).map f := sorry

/-- Compute a first-page target map by conjugating the source map with the inverse comparison. -/
@[reassoc, stacks 012O "target-map computation through the generic first-page comparison"]
theorem pageOneComparison_target_map (p q : ℤ)
    {S T : Realization (C := C)} (f : S ⟶ T) :
    (pageOneComparison (C := C) p q).inv.app S ≫
        (pageOneSource (C := C) p q).map f ≫
        (pageOneComparison (C := C) p q).hom.app T =
      (pageOneTarget (C := C) p q).map f := sorry

end CategoryTheory.FilteredComplex.SpectralSequence.Realization
