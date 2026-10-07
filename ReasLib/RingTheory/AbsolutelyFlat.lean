module

public import ReasLib.RingTheory.Flat.Localization.AtPrime
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Absolutely flat rings

This file owns the ring-level notion of absolute flatness.  The elementwise von Neumann regular
criterion is used as the universe-independent class field; flatness of every module is exposed as
the canonical characterization and as a reusable instance.

@stack 092B
@stack 092F
-/

@[expose] public section

universe u v w

/-- A commutative ring is absolutely flat when every element admits a von Neumann regular
factorization.  This is equivalent to flatness of every module. -/
@[stacks 092B "absolutely flat ring"]
class IsAbsolutelyFlatRing (R : Type u) [CommRing R] : Prop where
  /-- Every element is a multiple of its square. -/
  exists_factor (a : R) : ∃ b : R, a = a ^ 2 * b

namespace IsAbsolutelyFlatRing

variable (R : Type u) [CommRing R]

/-- Absolute flatness is equivalent to flatness of every module in any fixed universe. -/
@[stacks 092B "all modules are flat"]
theorem iff_forall_module_flat :
    IsAbsolutelyFlatRing R ↔
      ∀ (M : Type v) [AddCommGroup M] [Module R M], Module.Flat R M := sorry

/-- Every module over an absolutely flat ring is flat. -/
@[stacks 092B "modules over an absolutely flat ring are flat"]
instance instModuleFlat {M : Type w} [AddCommGroup M] [Module R M]
    [IsAbsolutelyFlatRing R] : Module.Flat R M := sorry

/-- Every field is an absolutely flat ring. -/
@[stacks 092B "fields are absolutely flat"]
instance instField (K : Type v) [Field K] : IsAbsolutelyFlatRing K := sorry

/-- A dependent product of absolutely flat rings is absolutely flat. -/
@[stacks 092B "products of absolutely flat rings"]
instance instPi {ι : Type v} (A : ι → Type w) [∀ i, CommRing (A i)]
    [∀ i, IsAbsolutelyFlatRing (A i)] : IsAbsolutelyFlatRing (∀ i, A i) := sorry

/-- A localization of an absolutely flat ring is absolutely flat.  This is an explicit theorem,
rather than an instance, because the localized ring does not determine its chosen base ring and
multiplicative subset. -/
theorem of_isLocalization (M : Submonoid R) (S : Type v) [CommRing S] [Algebra R S]
    [IsLocalization M S] [IsAbsolutelyFlatRing R] : IsAbsolutelyFlatRing S := sorry

/-- Every prime localization of an absolutely flat ring is a field. -/
@[stacks 092F "prime localizations are fields"]
theorem isField_localizationAtPrime [IsAbsolutelyFlatRing R] (p : PrimeSpectrum R) :
    IsField (Localization.AtPrime p.asIdeal) := sorry

end IsAbsolutelyFlatRing
