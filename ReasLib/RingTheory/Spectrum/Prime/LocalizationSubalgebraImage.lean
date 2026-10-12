/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

noncomputable section

open MvPolynomial Localization PrimeSpectrum

universe u

namespace YxInv

/-- The localization `k[x, y, x⁻¹]` of `k[x, y]` away from `X 0`. -/
abbrev xyAwayX (k : Type u) [CommRing k] : Type u :=
  Away (X 0 : MvPolynomial (Fin 2) k)

/-- The `k`-algebra structure on `k[x, y, x⁻¹]` induced by the polynomial algebra. -/
instance instAlgebra {k : Type u} [CommRing k] : Algebra k (xyAwayX k) :=
  ((algebraMap (MvPolynomial (Fin 2) k) (xyAwayX k)).comp
    (algebraMap k (MvPolynomial (Fin 2) k))).toAlgebra

/-- The element `yx⁻¹` in the localization `k[x, y, x⁻¹]`. -/
def yxInv (k : Type u) [CommRing k] : xyAwayX k :=
  algebraMap (MvPolynomial (Fin 2) k) (xyAwayX k) (X 1) * Away.invSelf (X 0)

/-- The polynomial substitution sending `x` to `x` and `y` to `xz`. -/
def yDivX (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0, X 0 * X 1]

/-- The algebra map sending `x` to `x` and `z` to `yx⁻¹`. -/
def yDivXToLocalization (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →ₐ[k] xyAwayX k :=
  aeval ![algebraMap (MvPolynomial (Fin 2) k) (xyAwayX k) (X 0), yxInv k]

/-- The subalgebra `k[x, yx⁻¹]` of `k[x, y, x⁻¹]`. -/
abbrev yxInvAdjoin (k : Type u) [CommRing k] : Subalgebra k (xyAwayX k) :=
  (yDivXToLocalization k).range

/-- The carrier of the subalgebra `k[x, yx⁻¹]`. -/
abbrev YxInvRing (k : Type u) [CommRing k] : Type u := yxInvAdjoin k

/-- The inclusion `k[x, y] ⟶ k[x, yx⁻¹]` into the localization subalgebra. -/
def yxInvInclusion (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →ₐ[k] YxInvRing k :=
  (yDivXToLocalization k).rangeRestrict.comp (yDivX k)

end YxInv

/-- The image of the inclusion is `D(x) ∪ V(x, y)` on prime spectra. -/
theorem yxInvInclusion_comap_range (k : Type u) [Field k] [IsAlgClosed k] :
    Set.range (comap (YxInv.yxInvInclusion k).toRingHom) =
      (basicOpen (X 0 : MvPolynomial (Fin 2) k) :
          Set (PrimeSpectrum (MvPolynomial (Fin 2) k))) ∪
        PrimeSpectrum.zeroLocus ({X 0, X 1} : Set (MvPolynomial (Fin 2) k)) := sorry
