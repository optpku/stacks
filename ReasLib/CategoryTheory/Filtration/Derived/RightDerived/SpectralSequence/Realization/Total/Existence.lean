/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Existence
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total.Constructors
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of total unbounded right-derived realization maps

This leaf lifts the generic realization-map existence theorem to the total realization category.
The base equation is part of the conclusion, so downstream constructions can use the total
morphism without rebuilding a dependent transport or unpacking the displayed category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

/-- A map of filtered complexes admits total realization objects and a total morphism whose base
arrow is exactly the prescribed map. -/
@[stacks 0BKK "existence of a total right-derived realization morphism"]
theorem existsMap [IsGrothendieckAbelian.{w} A]
    {K L : FilteredComplex A} (f : K ⟶ L) :
    ∃ (S : Realization F K) (T : Realization F L)
      (m : Total.of F S ⟶ Total.of F T), m.base = f := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization.Total
