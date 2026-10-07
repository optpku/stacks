module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Convergence
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total
import Mathlib.Tactic.CrossRefAttribute

/-!
# Convergence of total unbounded right-derived realizations

This leaf transports the generic realization convergence criteria across the total displayed
category.  It keeps the hypotheses on the source filtered complex and the conclusions on the
stored associated spectral sequence, so downstream users do not have to unpack `S.obj`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace Total

/-- Stagewise vanishing and stabilization make a total realization bounded. -/
@[stacks 0BKK "boundedness of a total unbounded right-derived spectral sequence"]
theorem isBounded (S : Realization.Total F)
    (hvanish : RightDerived.StageCohomology.eventuallyVanishesAbove F S.base)
    (hstabilize : RightDerived.StageCohomology.eventuallyStabilizesBelow F S.base) :
    S.obj.sequence.IsBounded := sorry

/-- Stagewise vanishing and stabilization make the total realization filtration finite. -/
@[stacks 0BKK "finite abutment filtration of a total right-derived realization"]
theorem finite (S : Realization.Total F)
    (hvanish : RightDerived.StageCohomology.eventuallyVanishesAbove F S.base)
    (hstabilize : RightDerived.StageCohomology.eventuallyStabilizesBelow F S.base) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.obj.filtered := sorry

/-- Stagewise vanishing and stabilization imply convergence of a total realization. -/
@[stacks 0BKK "convergence of a total unbounded right-derived spectral sequence"]
theorem converges (S : Realization.Total F)
    (hvanish : RightDerived.StageCohomology.eventuallyVanishesAbove F S.base)
    (hstabilize : RightDerived.StageCohomology.eventuallyStabilizesBelow F S.base) :
    FilteredComplex.Cohomology.Convergence.Converges
      S.obj.filtered S.obj.sequence := sorry

/-- Generic model stage criteria make a total realization bounded. -/
@[stacks 0BKK "generic-model boundedness of a total right-derived realization"]
theorem isBounded_of_generic (S : Realization.Total F)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.obj.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.obj.resolution)) :
    S.obj.sequence.IsBounded := sorry

/-- Generic model stage criteria make the total realization filtration finite. -/
@[stacks 0BKK "generic-model finite filtration of a total right-derived realization"]
theorem finite_of_generic (S : Realization.Total F)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.obj.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.obj.resolution)) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.obj.filtered := sorry

/-- Generic model stage criteria imply convergence of a total realization. -/
@[stacks 0BKK "generic-model convergence of a total right-derived realization"]
theorem converges_of_generic (S : Realization.Total F)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.obj.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.obj.resolution)) :
    FilteredComplex.Cohomology.Convergence.Converges
      S.obj.filtered S.obj.sequence := sorry

end Total

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization
