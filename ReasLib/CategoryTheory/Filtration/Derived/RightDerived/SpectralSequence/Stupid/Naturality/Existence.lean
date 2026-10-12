/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Definition

/-!
# Existence of Stupid-Filtration Realization Maps

This file gives the Grothendieck-source existence interface for compatible stupid-filtration
right-derived realizations of a cochain map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace Realization

/-- Compatible stupid-filtration realizations exist for every cochain map in a Grothendieck source.

The theorem packages the choices needed by downstream functoriality arguments; the chosen page
and abutment comparisons remain fields of the resulting realizations. -/
@[stacks 0FLK "existence of maps of stupid-filtration realizations"]
theorem existsMap [IsGrothendieckAbelian.{w} A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    ∃ (S : Realization F K) (T : Realization F L), Nonempty (Map F f S T) := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
