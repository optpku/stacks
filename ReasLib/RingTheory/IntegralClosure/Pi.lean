/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Algebra.Pi
public import ReasLib.RingTheory.Localization.TotalQuotient
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integrality in finite products

Integrality in a finite dependent product is equivalent to integrality in
every coordinate. This also describes its integral closure and its property of
being integrally closed.
-/

universe u v w

namespace IsIntegral

/-- Integrality in a finite product is componentwise integrality.

The rings and algebras may vary with the index. The hypothesis `Finite ι`
suffices, so no chosen `Fintype` structure is required.
-/
@[stacks 0CY8 "finite dependent-product integrality criterion"]
theorem pi_iff {ι : Type u} [Finite ι] {R : ι → Type v} {S : ι → Type w}
    [∀ i, CommRing (R i)] [∀ i, Ring (S i)] [∀ i, Algebra (R i) (S i)] {s : Π i, S i} :
    IsIntegral (Π i, R i) s ↔ ∀ i, IsIntegral (R i) (s i) := sorry

/-- Integrality in a finite product of algebras over one fixed commutative ring is equivalent to
integrality in every coordinate. -/
@[stacks 0CY8 "constant-base finite dependent-product integrality criterion"]
theorem pi_iff_of_constant {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
    {S : ι → Type w} [∀ i, Ring (S i)] [∀ i, Algebra R (S i)] {s : Π i, S i} :
    IsIntegral R s ↔ ∀ i, IsIntegral R (s i) := sorry

end IsIntegral

/-- Membership in the integral closure of a finite product over one fixed base ring is
componentwise membership. -/
@[stacks 0CY9 "constant-base finite-product integral-closure membership"]
theorem mem_integralClosure_pi_iff_of_constant {R : Type u} [CommRing R]
    {ι : Type v} [Finite ι] {S : ι → Type w}
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] {s : Π i, S i} :
    s ∈ integralClosure R (Π i, S i) ↔
      ∀ i, s i ∈ integralClosure R (S i) := sorry

/-- Membership in the integral closure of a finite dependent product is
componentwise membership in the corresponding integral closures. -/
@[stacks 0CY9 "finite dependent-product integral-closure membership"]
theorem mem_integralClosure_pi_iff {ι : Type u} [Finite ι]
    {R : ι → Type v} {S : ι → Type w}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
    {s : Π i, S i} :
    s ∈ integralClosure (Π i, R i) (Π i, S i) ↔
      ∀ i, s i ∈ integralClosure (R i) (S i) := sorry

/-- A dependent product algebra is integrally closed exactly when
each component algebra is integrally closed.  Finiteness supplies one common degree for the
coordinatewise integral equations. -/
@[stacks 0CY9 "dependent-product integral closedness"]
theorem isIntegrallyClosedIn_pi_iff {ι : Type u} [Finite ι]
    {R : ι → Type v} {S : ι → Type w}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)] :
    IsIntegrallyClosedIn (Π i, R i) (Π i, S i) ↔
      ∀ i, IsIntegrallyClosedIn (R i) (S i) := sorry

namespace integralClosure

/-- The total-quotient comparison restricts to a map from the integral closure
of a ring to the product of the integral closures of its minimal-prime
quotients. -/
noncomputable def totalQuotientToFractionRingPi (R : Type u) [CommRing R] :
    integralClosure R (Localization.totalQuotientRing R) →+*
      ((q : minimalPrimes R) →
        integralClosure (R ⧸ q.1) (FractionRing (R ⧸ q.1))) := by
  classical
  refine RingHom.pi fun q ↦ ?_
  let qQuot := R ⧸ q.1
  have hqMap :
      nonZeroDivisors R ≤
        Submonoid.comap (Ideal.Quotient.mk q.1) (nonZeroDivisors qQuot) := by
    intro x hx
    have hx_not_mem_q : x ∉ q.1 := by
      intro hxq
      exact Set.disjoint_left.mp
        (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes q.2) hxq hx
    change Ideal.Quotient.mk q.1 x ∈ nonZeroDivisors qQuot
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun hxq ↦ hx_not_mem_q (Ideal.Quotient.eq_zero_iff_mem.mp hxq)
  let qMapHom : Localization.totalQuotientRing R →+* FractionRing qQuot :=
    IsLocalization.map (FractionRing qQuot) (Ideal.Quotient.mk q.1) hqMap
  let qMap : Localization.totalQuotientRing R →ₐ[R] FractionRing qQuot :=
    { toRingHom := qMapHom
      commutes' := fun r ↦ by
        exact IsLocalization.map_eq hqMap r }
  exact
    RingHom.codRestrict
      (qMap.toRingHom.comp
        (integralClosure R (Localization.totalQuotientRing R)).val.toRingHom)
      (integralClosure qQuot (FractionRing qQuot)).toSubring
      (fun x ↦ by
        change IsIntegral qQuot
          (qMap ((integralClosure R (Localization.totalQuotientRing R)).val x))
        exact IsIntegral.tower_top (IsIntegral.map qMap x.2))

/-- In each coordinate, the integral-closure comparison is the underlying
total-quotient comparison. -/
theorem totalQuotientToFractionRingPi_apply (R : Type u) [CommRing R]
    (x : integralClosure R (Localization.totalQuotientRing R))
    (q : minimalPrimes R) :
    ((totalQuotientToFractionRingPi R x q :
        integralClosure (R ⧸ q.1) (FractionRing (R ⧸ q.1))) :
      FractionRing (R ⧸ q.1)) =
      Localization.totalQuotientToFractionRingPi R x.1 q := sorry

/-- For a reduced ring with finitely many minimal primes, its integral closure
in the total quotient ring is the product of the integral closures of the
minimal-prime quotients in their fraction rings. -/
@[stacks 035P]
theorem totalQuotientToFractionRingPi_bijective (R : Type u) [CommRing R]
    [IsReduced R] (hfinite : (minimalPrimes R).Finite) :
    Function.Bijective (totalQuotientToFractionRingPi R) := sorry

end integralClosure
