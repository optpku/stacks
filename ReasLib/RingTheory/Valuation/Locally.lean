module

public import ReasLib.RingTheory.Flat.Localization.AtPrime
public import ReasLib.RingTheory.Valuation.Characterization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Rings with valuation localizations

The predicate `Ring.LocallyValuation R` packages the assertion that every prime localization of
`R` is a valuation domain.  Keeping the domain witness inside the predicate matches Mathlib's
canonical `ValuationRing` class without installing proof-local instances at use sites.
@stack 092S
-/

@[expose] public section

universe u v

namespace Ring

/-- A commutative ring is locally valuation when every localization at a prime is a valuation
domain. -/
@[stacks 092S "rings whose prime localizations are valuation rings"]
def LocallyValuation (R : Type u) [CommRing R] : Prop :=
  ∀ p : PrimeSpectrum R,
    ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
      ValuationRing (Localization.AtPrime p.asIdeal)

namespace LocallyValuation

variable {R : Type u} [CommRing R]

/-- Every ideal of a locally valuation ring is flat. -/
@[stacks 092S "flat ideals in a locally valuation ring"]
theorem ideal_flat (h : Ring.LocallyValuation R) (I : Ideal R) :
    Module.Flat R I := sorry

/-- Flatness of all ideals implies that every prime localization is a valuation ring. -/
@[stacks 092S "locally valuation from flat ideals"]
theorem of_ideals_flat (h : ∀ I : Ideal R, Module.Flat R I) :
    Ring.LocallyValuation R := sorry

/-- A ring is locally valuation exactly when all of its ideals are flat. -/
@[stacks 092S "locally valuation iff all ideals are flat"]
theorem iff_ideals_flat :
    Ring.LocallyValuation R ↔ ∀ I : Ideal R, Module.Flat R I := sorry

/-- Every submodule of a flat module over a locally valuation ring is flat. -/
@[stacks 092S "flat submodules over a locally valuation ring"]
theorem submodule_flat {M : Type v} [AddCommMonoid M] [Module R M]
    (h : Ring.LocallyValuation R) (hM : Module.Flat R M) (N : Submodule R M) :
    Module.Flat R N := sorry

end LocallyValuation

end Ring
