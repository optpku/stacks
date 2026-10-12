/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Total.Constructors
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence in the total category of stupid-filtration realizations

This leaf exposes the Grothendieck-source existence theorem directly in the total category.  The
base equality is part of the returned proposition, so downstream constructions do not need to
rebuild `Total.of` and `Hom.ofMap` by hand.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

/-- Grothendieck-source existence of a total stupid-filtration map over a prescribed cochain map.

The returned total objects are constructed by `of`, and the returned total morphism has base
component exactly `f`.
-/
@[stacks 0FLK "existence of total stupid-filtration realization maps"]
theorem existsMap [IsGrothendieckAbelian.{w} A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    ∃ (S : Realization F K) (T : Realization F L)
      (m : of F S ⟶ of F T), m.base = f := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total
