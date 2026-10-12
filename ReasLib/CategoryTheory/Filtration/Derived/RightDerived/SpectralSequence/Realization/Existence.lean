/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of unbounded filtered right-derived realizations

Grothendieck abelian sources provide realizations and compatible realization maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace SpectralSequence.Realization

/-- Every filtered complex in a Grothendieck abelian source admits a right-derived
spectral-sequence realization. -/
@[stacks 0BKK]
theorem nonempty [IsGrothendieckAbelian.{w} A] (K : FilteredComplex A) :
    Nonempty (Realization F K) := sorry

/-- A map of filtered complexes admits compatible choices of right-derived realizations. -/
@[stacks 0BKK "functoriality"]
theorem existsMap [IsGrothendieckAbelian.{w} A]
    {K L : FilteredComplex A} (f : K ⟶ L) :
    ∃ (S : Realization F K) (T : Realization F L), Nonempty (Map F f S T) := sorry

end SpectralSequence.Realization

end CategoryTheory.FilteredComplex.RightDerived

