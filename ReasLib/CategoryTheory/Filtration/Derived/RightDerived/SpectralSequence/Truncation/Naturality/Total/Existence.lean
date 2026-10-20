/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Total.Constructors
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence in the total category of truncation-filtration realizations

The representative-lift hypothesis remains explicit.  The total bridge returns only the
category-level morphism, while `existsMapOfLift` in the realization namespace remains the owner of
the prescribed lift specification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

/-- A nonempty selected-preimage lift yields a total truncation-filtration map over `f`. -/
@[stacks 0BKM "existence of total truncation realization maps"]
theorem existsMap [IsGrothendieckAbelian.{w} A]
    {K L : DerivedCategory A} (f : K ⟶ L)
    (h_lift : Nonempty (DerivedCategory.Preimage.Lift f)) :
    ∃ (S : Realization F K) (T : Realization F L)
      (m : of F S ⟶ of F T), m.base = f := sorry

/-- Total truncation maps over `f` exist exactly when `f` admits a selected-preimage lift. -/
@[stacks 0BKM "characterization of total truncation realization-map existence"]
theorem existsMap_iff_nonemptyLift [IsGrothendieckAbelian.{w} A]
    {K L : DerivedCategory A} (f : K ⟶ L) :
    (∃ (S : Realization F K) (T : Realization F L)
      (m : of F S ⟶ of F T), m.base = f) ↔
      Nonempty (DerivedCategory.Preimage.Lift f) := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total
