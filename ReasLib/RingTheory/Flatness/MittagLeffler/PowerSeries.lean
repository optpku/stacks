module

public import Mathlib.RingTheory.PowerSeries.Basic
public import ReasLib.RingTheory.Flatness.MittagLeffler.Pi

@[expose] public section

/-!
# Formal Power Series as Flat Mittag-Leffler Modules

@stack 059T
@stack 059Y

Multivariate formal power series are products of copies of the coefficient ring.  This leaf
installs the resulting flat and Mittag-Leffler instances on the canonical Mathlib objects rather
than relying on reducible unfolding at each use site.
-/

universe u v

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {σ : Type v}

/-- Multivariate formal power series over a coherent ring are flat over the coefficient ring. -/
@[stacks 059T "flatness of multivariate formal power series"]
instance mvPowerSeries [IsCoherentRing R] : Module.Flat R (MvPowerSeries σ R) := sorry

end Module.Flat

namespace Module.MittagLeffler

variable {R : Type u} [CommRing R]
variable {σ : Type v}

/-- Multivariate formal power series over a Noetherian ring are Mittag-Leffler over the
coefficient ring. -/
@[stacks 059T "Mittag-Leffler multivariate formal power series"]
instance mvPowerSeries [IsNoetherianRing R] : MittagLeffler R (MvPowerSeries σ R) := sorry

end Module.MittagLeffler

namespace PowerSeries

/-- The coefficient of multiplication by an integer constant is the corresponding integer
multiple of the coefficient. -/
theorem coeff_intCast_mul (n : ℤ) (f : ℤ⟦X⟧) (i : ℕ) :
    coeff i ((n : ℤ⟦X⟧) * f) = n * coeff i f := sorry

/-- Coefficients commute with the canonical integer scalar action on integer power series. -/
theorem coeff_int_smul (n : ℤ) (f : ℤ⟦X⟧) (i : ℕ) :
    coeff i (n • f) = n * coeff i f := sorry

/-- The canonical integer-module structure on `ℤ⟦X⟧` is flat. -/
@[stacks 059Y "flatness of integer power series"]
instance intFlat : Module.Flat ℤ ℤ⟦X⟧ := sorry

/-- The canonical integer-module structure on `ℤ⟦X⟧` is Mittag-Leffler. -/
@[stacks 059Y "Mittag-Leffler integer power series"]
instance intMittagLeffler : Module.MittagLeffler ℤ ℤ⟦X⟧ := sorry

end PowerSeries

namespace MvPowerSeries

variable {R : Type u} [CommRing R]

/-- Arbitrary-variable multivariate formal power series over a Noetherian ring are flat and
Mittag-Leffler over the coefficient ring. -/
theorem flat_mittagLeffler [IsNoetherianRing R] (σ : Type v) :
    Module.Flat R (MvPowerSeries σ R) ∧
      Module.MittagLeffler R (MvPowerSeries σ R) := sorry

/-- Lemma 10.91.4, tag `059T`: finite-variable formal power series over a Noetherian ring are flat
and Mittag-Leffler over the coefficient ring. -/
@[stacks 059T]
theorem fin_flat_mittagLeffler [IsNoetherianRing R] (n : ℕ) :
    Module.Flat R (MvPowerSeries (Fin n) R) ∧
      Module.MittagLeffler R (MvPowerSeries (Fin n) R) := sorry

end MvPowerSeries
