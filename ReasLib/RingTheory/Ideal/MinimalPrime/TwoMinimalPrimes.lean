/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.Depth

@[expose] public section

universe u

noncomputable section

open CategoryTheory
open scoped ENat

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The canonical map from `R` to the product of the quotients by two ideals. -/
def quotientProdMk (p q : Ideal R) : R →ₗ[R] (R ⧸ p) × (R ⧸ q) :=
  LinearMap.prod p.mkQ q.mkQ

/-- The map `quotientProdMk p q` sends `x` to its two residue classes. -/
theorem quotientProdMk_apply (p q : Ideal R) (x : R) :
    quotientProdMk p q x = (Quotient.mk p x, Quotient.mk q x) :=
  sorry

/-- The canonical difference map from two ideal quotients to the quotient by their sum. -/
def quotientSupSub (p q : Ideal R) : (R ⧸ p) × (R ⧸ q) →ₗ[R] R ⧸ (p + q) :=
  (Quotient.factorₐ R le_sup_left).toLinearMap.coprod
    (-(Quotient.factorₐ R le_sup_right).toLinearMap)

/-- The difference map sends two residue classes to the residue class of their difference. -/
theorem quotientSupSub_apply (p q : Ideal R) (y z : R) :
    quotientSupSub p q (Quotient.mk p y, Quotient.mk q z) = Quotient.mk (p + q) (y - z) :=
  sorry

/-- The composite of the canonical product and difference maps is zero. -/
theorem quotientSupSub_comp_quotientProdMk (p q : Ideal R) :
    (quotientSupSub p q).comp (quotientProdMk p q) = 0 :=
  sorry

/-- The short complex formed by the two quotient maps for ideals `p` and `q`. -/
def quotientProdSupShortComplex (p q : Ideal R) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero (quotientProdMk p q) (quotientSupSub p q)
    (quotientSupSub_comp_quotientProdMk p q)

/-- If the two distinct minimal primes are exactly `p` and `q`, the quotient sequence is short exact. -/
theorem quotientProdSup_shortExact
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R]
    {p q : Ideal R} (hmin : minimalPrimes R = {p, q}) (hne : p ≠ q) :
    (quotientProdSupShortComplex p q).ShortExact :=
  sorry

/-- If the two minimal primes are exactly `p` and `q`, depth at least two forces the quotient by
their sum to have Krull dimension at least one. -/
theorem ringKrullDim_quotient_add_ge_one_of_moduleDepth_ge_two
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R]
    {p q : Ideal R} (hmin : minimalPrimes R = {p, q}) (hne : p ≠ q)
    (hdepth : (2 : ℕ∞) ≤ moduleDepth R R) :
    1 ≤ ringKrullDim (R ⧸ (p + q)) :=
  sorry

end Ideal
