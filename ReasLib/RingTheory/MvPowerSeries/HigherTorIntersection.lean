module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Field.NegOnePow
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Length
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

namespace MvPowerSeries.HigherTorIntersection

/-- The four-variable formal power-series ring over the complex numbers. -/
abbrev PowerSeriesRing : Type :=
  MvPowerSeries (Fin 4) ℂ

/-- The first coordinate in the four-variable formal power-series ring. -/
def x : PowerSeriesRing :=
  MvPowerSeries.X (0 : Fin 4)

/-- The second coordinate in the four-variable formal power-series ring. -/
def y : PowerSeriesRing :=
  MvPowerSeries.X (1 : Fin 4)

/-- The third coordinate in the four-variable formal power-series ring. -/
def z : PowerSeriesRing :=
  MvPowerSeries.X (2 : Fin 4)

/-- The fourth coordinate in the four-variable formal power-series ring. -/
def w : PowerSeriesRing :=
  MvPowerSeries.X (3 : Fin 4)

/-- The ideal `(xz, xw, yz, yw)` defining the union of two coordinate planes. -/
def reduciblePlaneIdeal : Ideal PowerSeriesRing :=
  Ideal.span ({x * z, x * w, y * z, y * w} : Set PowerSeriesRing)

/-- The ideal `(x - z, y - w)` defining the diagonal plane. -/
def diagonalPlaneIdeal : Ideal PowerSeriesRing :=
  Ideal.span ({x - z, y - w} : Set PowerSeriesRing)

/-- The intersection quotient of the union of two coordinate planes with the
diagonal plane has length three. -/
theorem quotientLength_eq_three :
    Module.length PowerSeriesRing
      (PowerSeriesRing ⧸ (reduciblePlaneIdeal ⊔ diagonalPlaneIdeal)) = 3 := sorry

/-- The signed Euler characteristic of the higher `Tor` modules of the two plane
quotients is two. -/
theorem torEulerCharacteristic_eq_two :
    ∑ᶠ i : ℕ, (Int.negOnePow i : ℤ) *
      ((Module.length PowerSeriesRing
        (ModuleCat.Tor.obj i
          (ModuleCat.of PowerSeriesRing (PowerSeriesRing ⧸ reduciblePlaneIdeal))
          (ModuleCat.of PowerSeriesRing (PowerSeriesRing ⧸ diagonalPlaneIdeal)))).toNat : ℤ) =
      2 := sorry

end MvPowerSeries.HigherTorIntersection
