/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Views
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.QuasiIso

/-!
# Quasi-Isomorphism API for Strict Filtered-Injective Resolutions

This leaf records the semantic content of the comparison carried by a strict filtered-injective
resolution at the bounded-complex level.  The filtered comparison is a finite filtered
quasi-isomorphism; consequently its graded-piece and underlying comparison maps are ordinary
quasi-isomorphisms.  The data maps themselves remain owned by `Resolution.Views`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.FilteredInjectivePlus.Resolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The bounded comparison of a strict filtered-injective resolution is a finite filtered
quasi-isomorphism. -/
@[stacks 05TW "bounded filtered quasi-isomorphism of a strict filtered-injective resolution"]
theorem comparison_quasiIso
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) :
    FilteredObject.Finite.Plus.QuasiIso C R.comparison := sorry

/-- The comparison on every graded piece of a strict filtered-injective resolution is an
ordinary quasi-isomorphism. -/
@[stacks 05TW "graded-piece quasi-isomorphism of a strict filtered-injective resolution"]
theorem gradedPieceComparison_quasiIso
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) (p : ℤ) :
    _root_.QuasiIso (R.gradedPieceComparison p).hom := sorry

/-- Forgetting the filtration on a strict filtered-injective resolution comparison gives an
ordinary quasi-isomorphism. -/
@[stacks 05TW "underlying quasi-isomorphism of a strict filtered-injective resolution"]
theorem underlyingComparison_quasiIso
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) :
    _root_.QuasiIso R.underlyingComparison.hom := sorry

end CochainComplex.FilteredInjectivePlus.Resolution
