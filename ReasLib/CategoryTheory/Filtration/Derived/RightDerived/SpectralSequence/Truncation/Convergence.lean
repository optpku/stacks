module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Convergence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generic-model convergence for truncation realizations

The source-facing bounded-below theorem remains in the truncation owner.  This leaf adds the
generic model criteria used by downstream arguments that already work at the filtered-complex
level.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- Generic model stage criteria make a truncation realization bounded. -/
@[stacks 0BKM "generic-model boundedness of a truncation realization"]
theorem isBounded_of_generic {K : DerivedCategory A} (S : Realization F K)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.original.resolution)) :
    S.sequence.IsBounded := sorry

/-- Generic model stage criteria make a truncation realization filtration finite. -/
@[stacks 0BKM "generic-model finite filtration of a truncation realization"]
theorem finite_of_generic {K : DerivedCategory A} (S : Realization F K)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.original.resolution)) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- Generic model stage criteria imply renumbered convergence of a truncation realization. -/
@[stacks 0BKM "generic-model convergence of a truncation realization"]
theorem converges_of_generic {K : DerivedCategory A} (S : Realization F K)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.original.resolution)) :
    FilteredComplex.Cohomology.Convergence.ConvergesViaRenumbering
      S.filtered S.originalSequence S.sequence := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization
