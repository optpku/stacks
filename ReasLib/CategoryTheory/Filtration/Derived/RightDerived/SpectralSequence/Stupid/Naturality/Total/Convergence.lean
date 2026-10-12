/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Total
import Mathlib.Tactic.CrossRefAttribute

/-!
# Convergence of total stupid-filtration realizations

The bounded-below source condition is stated through Mathlib's canonical `CochainComplex.plus`
property.  The conclusions are expressed on the realization stored in the total category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- A bounded-below total stupid realization has a bounded first-page sequence. -/
@[stacks 0FLK "boundedness of a total stupid-filtration spectral sequence"]
theorem isBounded (S : Realization.Total F)
    (hK : CochainComplex.plus A S.base) :
    S.obj.sequence.IsBounded := sorry

/-- A bounded-below total stupid realization has a finite abutment filtration. -/
@[stacks 0FLK "finite filtration of a total stupid realization"]
theorem finite (S : Realization.Total F)
    (hK : CochainComplex.plus A S.base) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.obj.filtered := sorry

/-- A bounded-below total stupid realization converges to its abutment. -/
@[stacks 0FLK "convergence of a total stupid-filtration spectral sequence"]
theorem converges (S : Realization.Total F)
    (hK : CochainComplex.plus A S.base) :
    FilteredComplex.Cohomology.Convergence.Converges
      S.obj.filtered S.obj.sequence := sorry

/-- Generic model stage criteria make a total stupid realization bounded. -/
@[stacks 0FLK "generic-model boundedness of a total stupid realization"]
theorem isBounded_of_generic (S : Realization.Total F)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.obj.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.obj.original.resolution)) :
    S.obj.sequence.IsBounded := sorry

/-- Generic model stage criteria make the total stupid realization filtration finite. -/
@[stacks 0FLK "generic-model finite filtration of a total stupid realization"]
theorem finite_of_generic (S : Realization.Total F)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.obj.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.obj.original.resolution)) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.obj.filtered := sorry

/-- Generic model stage criteria imply convergence of a total stupid realization. -/
@[stacks 0FLK "generic-model convergence of a total stupid realization"]
theorem converges_of_generic (S : Realization.Total F)
    (hvanish : FilteredComplex.StageCohomology.eventuallyVanishesAbove
      (RightDerived.model F S.obj.original.resolution))
    (hstabilize : FilteredComplex.StageCohomology.eventuallyStabilizesBelow
      (RightDerived.model F S.obj.original.resolution)) :
    FilteredComplex.Cohomology.Convergence.Converges
      S.obj.filtered S.obj.sequence := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total
