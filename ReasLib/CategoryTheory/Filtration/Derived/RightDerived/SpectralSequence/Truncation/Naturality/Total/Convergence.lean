/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Total
import Mathlib.Tactic.CrossRefAttribute

/-!
# Convergence of total truncation-filtration realizations

Bounded-below derived objects give the canonical bounded and convergence conclusions for the
renumbered truncation spectral sequence.  This leaf keeps the source condition on the total base
object and avoids dependent unpacking of the stored realization.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- A bounded-below total truncation realization has a bounded renumbered sequence. -/
@[stacks 0BKM "boundedness of a total truncation-filtration spectral sequence"]
theorem isBounded (S : Realization.Total F)
    (hK : DerivedCategory.IsBoundedBelow S.base) :
    S.obj.sequence.IsBounded := sorry

/-- A bounded-below total truncation realization has a finite abutment filtration. -/
@[stacks 0BKM "finite filtration of a total truncation realization"]
theorem finite (S : Realization.Total F)
    (hK : DerivedCategory.IsBoundedBelow S.base) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.obj.filtered := sorry

/-- A bounded-below total truncation realization converges through its standard renumbering. -/
@[stacks 0BKM "convergence of a total truncation-filtration spectral sequence"]
theorem converges (S : Realization.Total F)
    (hK : DerivedCategory.IsBoundedBelow S.base) :
    FilteredComplex.Cohomology.Convergence.ConvergesViaRenumbering
      S.obj.filtered S.obj.originalSequence S.obj.sequence := sorry

/-- Generic model stage criteria make a total truncation realization bounded. -/
@[stacks 0BKM "generic-model boundedness of a total truncation realization"]
theorem isBounded_of_generic (S : Realization.Total F)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.obj.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.obj.original.resolution)) :
    S.obj.sequence.IsBounded := sorry

/-- Generic model stage criteria make the total truncation realization filtration finite. -/
@[stacks 0BKM "generic-model finite filtration of a total truncation realization"]
theorem finite_of_generic (S : Realization.Total F)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.obj.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.obj.original.resolution)) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.obj.filtered := sorry

/-- Generic model stage criteria imply renumbered convergence of a total truncation realization. -/
@[stacks 0BKM "generic-model convergence of a total truncation realization"]
theorem converges_of_generic (S : Realization.Total F)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.obj.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.obj.original.resolution)) :
    FilteredComplex.Cohomology.Convergence.ConvergesViaRenumbering
      S.obj.filtered S.obj.originalSequence S.obj.sequence := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total
