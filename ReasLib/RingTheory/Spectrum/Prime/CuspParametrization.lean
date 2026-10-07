module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

noncomputable section

open MvPolynomial Localization PrimeSpectrum

universe u

namespace Cusp

/-- The localization `k[t, 1 / (t - 1)]`. -/
abbrev cuspAway (k : Type u) [CommRing k] : Type u :=
  Away (Polynomial.X - 1 : Polynomial k)

/-- The `k`-algebra structure on `k[t, 1 / (t - 1)]`. -/
instance instAlgebra {k : Type u} [CommRing k] : Algebra k (cuspAway k) :=
  ((algebraMap (Polynomial k) (cuspAway k)).comp (algebraMap k (Polynomial k))).toAlgebra

/-- The localized parametrization sending `x` to `t²` and `y` to `t³`. -/
def cuspHom (k : Type u) [CommRing k] : MvPolynomial (Fin 2) k →ₐ[k] cuspAway k :=
  aeval ![algebraMap (Polynomial k) (cuspAway k) (Polynomial.X ^ 2),
    algebraMap (Polynomial k) (cuspAway k) (Polynomial.X ^ 3)]

end Cusp

/-- The image of the cusp parametrization is `V(y² - x³) \ {(1, 1)}`. -/
theorem cuspHom_comap_range (k : Type u) [Field k] [IsAlgClosed k] :
    Set.range (comap (Cusp.cuspHom k).toRingHom) =
      PrimeSpectrum.zeroLocus ({X 1 ^ 2 - X 0 ^ 3} : Set (MvPolynomial (Fin 2) k)) \
        {pointToPoint (![1, 1] : Fin 2 → k)} := sorry
