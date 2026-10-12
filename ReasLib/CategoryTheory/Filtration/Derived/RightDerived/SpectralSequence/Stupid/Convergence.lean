/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Convergence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generic-model convergence for stupid realizations

This leaf keeps the specialization symmetric with the generic realization API: hypotheses may be
stated directly on the selected right-derived model instead of being converted to a source-side
boundedness package first.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- Generic model stage criteria make a stupid realization bounded. -/
@[stacks 0FLK "generic-model boundedness of a stupid realization"]
theorem isBounded_of_generic {K : CochainComplex A ℤ} (S : Realization F K)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.original.resolution)) :
    S.sequence.IsBounded := sorry

/-- Generic model stage criteria make a stupid realization filtration finite. -/
@[stacks 0FLK "generic-model finite filtration of a stupid realization"]
theorem finite_of_generic {K : CochainComplex A ℤ} (S : Realization F K)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.original.resolution)) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- Generic model stage criteria imply convergence of a stupid realization. -/
@[stacks 0FLK "generic-model convergence of a stupid realization"]
theorem converges_of_generic {K : CochainComplex A ℤ} (S : Realization F K)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.original.resolution)) :
    FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization
