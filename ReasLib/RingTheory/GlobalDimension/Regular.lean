/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GlobalDimension.Basic

/-!
# Finite Global Dimension and Regular Rings

This leaf owns the global Noetherian comparison between finite global
dimension, regularity, and Krull dimension.  It exposes named directional
statements rather than a positional `List.TFAE` interface.

@stack 00OE
-/

@[expose] public section

universe u

namespace IsFiniteGlobalDimensionRing

/-- Stacks 00OE: a nontrivial Noetherian ring of finite global dimension is regular. -/
@[stacks 00OE "finite global dimension implies regularity"]
theorem isRegularRing
    {R : Type u} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    [IsFiniteGlobalDimensionRing R] :
    IsRegularRing R := sorry

/-- Stacks 00OE: on a nontrivial Noetherian ring of finite global dimension,
Krull dimension is the global dimension. -/
@[stacks 00OE "Krull dimension equals global dimension"]
theorem ringKrullDim_eq_globalDimension
    {R : Type u} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    [IsFiniteGlobalDimensionRing R] :
    ringKrullDim R = globalDimension R := sorry

/-- Stacks 00OE: finite global dimension with exact value `n` is equivalent to
regularity with Krull dimension `n`. -/
@[stacks 00OE "finite global dimension characterization"]
theorem exists_globalDimension_eq_iff
    {R : Type u} [CommRing R] [Nontrivial R] [IsNoetherianRing R] (n : ℕ) :
    (∃ _ : IsFiniteGlobalDimensionRing R, globalDimension R = n) ↔
      IsRegularRing R ∧ ringKrullDim R = n := sorry

/-- Stacks 00OE: regular maximal localizations with a common dimension bound
and a maximal localization attaining it give finite global dimension of that
exact value. -/
@[stacks 00OE "maximal-local global-dimension criterion"]
theorem exists_globalDimension_eq_of_regularAtMaximal
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (hregular : ∀ m : MaximalSpectrum R,
      IsRegularLocalRing (Localization.AtPrime m.asIdeal))
    (hbound : ∀ m : MaximalSpectrum R,
      ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n)
    (hrealize : ∃ m : MaximalSpectrum R,
      ringKrullDim (Localization.AtPrime m.asIdeal) = n) :
    ∃ _ : IsFiniteGlobalDimensionRing R, globalDimension R = n := sorry

end IsFiniteGlobalDimensionRing

namespace IsRegularRing

/-- Stacks 00OE: a regular ring whose Krull dimension is the natural number
`n` has finite global dimension exactly `n`. -/
@[stacks 00OE "regular rings have the expected global dimension"]
theorem exists_globalDimension_eq
    {R : Type u} [CommRing R] [IsRegularRing R] {n : ℕ}
    (h_dim : ringKrullDim R = n) :
    ∃ _ : IsFiniteGlobalDimensionRing R, globalDimension R = n := sorry

end IsRegularRing
