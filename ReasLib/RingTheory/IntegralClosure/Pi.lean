/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Algebra.Pi
public import ReasLib.RingTheory.Localization.TotalQuotient
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integrality in finite products

Integrality in a finite dependent product is equivalent to integrality in
every coordinate. This also describes its integral closure and its property of
being integrally closed.
-/

universe u v w

open Polynomial

namespace IsIntegral

/-- Integrality in a finite product is componentwise integrality.

The rings and algebras may vary with the index. The hypothesis `Finite ι`
suffices, so no chosen `Fintype` structure is required.
-/
@[stacks 0CY8 "finite dependent-product integrality criterion"]
theorem pi_iff {ι : Type u} [Finite ι] {R : ι → Type v} {S : ι → Type w}
    [∀ i, CommRing (R i)] [∀ i, Ring (S i)] [∀ i, Algebra (R i) (S i)] {s : Π i, S i} :
    IsIntegral (Π i, R i) s ↔ ∀ i, IsIntegral (R i) (s i) := by
  classical
  constructor
  · intro h i
    exact IsIntegral.map_of_comp_eq (Pi.evalRingHom R i) (Pi.evalRingHom S i) rfl h
  · intro h
    letI := Fintype.ofFinite ι
    choose p hp hpe using h
    have hlift (i : ι) : ∃ q : Polynomial (Π i, R i),
        q.map (Pi.evalRingHom R i) = p i ∧ q.Monic := by
      have hs : Function.Surjective (Pi.evalRingHom R i) := by
        intro x
        exact ⟨Function.update 0 i x, by simp⟩
      obtain ⟨q, hq, _, hqm⟩ := lifts_and_natDegree_eq_and_monic
        (mem_lifts_of_surjective hs (p i)) (hp i)
      exact ⟨q, hq, hqm⟩
    choose q hq hqm using hlift
    refine ⟨∏ i, q i, monic_prod_of_monic Finset.univ q (fun i _ ↦ hqm i), ?_⟩
    rw [← aeval_def]
    funext i
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem q (Finset.mem_univ i)
    rw [ht, map_mul, Pi.mul_apply]
    have hi : aeval s (q i) i = 0 := by
      change (Pi.evalRingHom S i) (eval₂ (algebraMap (Π i, R i) (Π i, S i)) s (q i)) = 0
      rw [hom_eval₂]
      change eval₂ ((algebraMap (R i) (S i)).comp (Pi.evalRingHom R i)) (s i) (q i) = 0
      rw [← eval₂_map, hq i]
      exact hpe i
    simp [hi]

/-- Integrality in a finite product of algebras over one fixed commutative ring is equivalent to
integrality in every coordinate. -/
@[stacks 0CY8 "constant-base finite dependent-product integrality criterion"]
theorem pi_iff_of_constant {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
    {S : ι → Type w} [∀ i, Ring (S i)] [∀ i, Algebra R (S i)] {s : Π i, S i} :
    IsIntegral R s ↔ ∀ i, IsIntegral R (s i) := by
  classical
  constructor
  · intro h i
    exact IsIntegral.map (Pi.evalAlgHom R S i) h
  · intro h
    letI := Fintype.ofFinite ι
    choose p hp hpe using h
    refine ⟨∏ i, p i, monic_prod_of_monic Finset.univ p (fun i _ ↦ hp i), ?_⟩
    rw [← aeval_def, aeval_pi_apply]
    funext i
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem p (Finset.mem_univ i)
    change aeval (s i) (∏ j, p j) = 0
    rw [hq, map_mul, aeval_def, hpe i, zero_mul]

end IsIntegral

/-- Membership in the integral closure of a finite product over one fixed base ring is
componentwise membership. -/
@[stacks 0CY9 "constant-base finite-product integral-closure membership"]
theorem mem_integralClosure_pi_iff_of_constant {R : Type u} [CommRing R]
    {ι : Type v} [Finite ι] {S : ι → Type w}
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] {s : Π i, S i} :
    s ∈ integralClosure R (Π i, S i) ↔
      ∀ i, s i ∈ integralClosure R (S i) :=
  IsIntegral.pi_iff_of_constant

/-- Membership in the integral closure of a finite dependent product is
componentwise membership in the corresponding integral closures. -/
@[stacks 0CY9 "finite dependent-product integral-closure membership"]
theorem mem_integralClosure_pi_iff {ι : Type u} [Finite ι]
    {R : ι → Type v} {S : ι → Type w}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
    {s : Π i, S i} :
    s ∈ integralClosure (Π i, R i) (Π i, S i) ↔
      ∀ i, s i ∈ integralClosure (R i) (S i) :=
  IsIntegral.pi_iff

/-- A dependent product algebra is integrally closed exactly when
each component algebra is integrally closed.  Finiteness supplies one common degree for the
coordinatewise integral equations. -/
@[stacks 0CY9 "dependent-product integral closedness"]
theorem isIntegrallyClosedIn_pi_iff {ι : Type u} [Finite ι]
    {R : ι → Type v} {S : ι → Type w}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)] :
    IsIntegrallyClosedIn (Π i, R i) (Π i, S i) ↔
      ∀ i, IsIntegrallyClosedIn (R i) (S i) := by
  classical
  constructor
  · intro h i
    obtain ⟨hinj, hcl⟩ := isIntegrallyClosedIn_iff.mp h
    apply isIntegrallyClosedIn_iff.mpr
    constructor
    · intro a b hab
      have hab' : algebraMap (Π i, R i) (Π i, S i) (Function.update (0 : Π i, R i) i a) =
          algebraMap (Π i, R i) (Π i, S i) (Function.update (0 : Π i, R i) i b) := by
        funext j
        change algebraMap (R j) (S j) (Function.update (0 : Π i, R i) i a j) =
          algebraMap (R j) (S j) (Function.update (0 : Π i, R i) i b j)
        by_cases hji : j = i
        · subst j
          simpa using hab
        · simp [hji]
      have := congr_fun (hinj hab') i
      simpa using this
    · intro x hx
      have hx' : IsIntegral (Π i, R i) (Function.update (0 : Π i, S i) i x) := by
        apply IsIntegral.pi_iff.mpr
        intro j
        by_cases hji : j = i
        · subst j
          simpa using hx
        · simpa [hji] using (isIntegral_zero : IsIntegral (R j) (0 : S j))
      obtain ⟨r, hr⟩ := hcl hx'
      refine ⟨r i, ?_⟩
      have hri := congr_fun hr i
      change algebraMap (R i) (S i) (r i) = Function.update (0 : Π i, S i) i x i at hri
      simpa using hri
  · intro h
    apply isIntegrallyClosedIn_iff.mpr
    constructor
    · intro a b hab
      funext i
      apply (isIntegrallyClosedIn_iff.mp (h i)).1
      exact congr_fun hab i
    · intro x hx
      choose r hr using fun i ↦
        (isIntegrallyClosedIn_iff.mp (h i)).2 (IsIntegral.pi_iff.mp hx i)
      exact ⟨r, funext hr⟩

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
      Localization.totalQuotientToFractionRingPi R x.1 q := by
  rfl

/-- For a reduced ring with finitely many minimal primes, its integral closure
in the total quotient ring is the product of the integral closures of the
minimal-prime quotients in their fraction rings. -/
@[stacks 035P]
theorem totalQuotientToFractionRingPi_bijective (R : Type u) [CommRing R]
    [IsReduced R] (hfinite : (minimalPrimes R).Finite) :
    Function.Bijective (totalQuotientToFractionRingPi R) := by
  classical
  letI := hfinite.fintype
  let f : Localization.totalQuotientRing R →ₐ[R]
      ((q : minimalPrimes R) → FractionRing (R ⧸ q.1)) :=
    { toRingHom := Localization.totalQuotientToFractionRingPi R
      commutes' := fun r ↦ by
        funext q
        exact Localization.totalQuotientToFractionRingPi_apply R r q }
  have hf : Function.Bijective f :=
    Localization.totalQuotientToFractionRingPi_bijective R hfinite
  constructor
  · intro x y h
    apply Subtype.ext
    apply hf.1
    funext q
    exact congr_arg Subtype.val (congr_fun h q)
  · intro y
    obtain ⟨x, hx⟩ := hf.2 (fun q ↦ (y q).1)
    have hy : IsIntegral R (fun q ↦ (y q).1) := by
      apply IsIntegral.pi_iff_of_constant.mpr
      intro q
      exact isIntegral_trans (R := R) (A := R ⧸ q.1) (y q).1 (y q).2
    have hxint : IsIntegral R x := (isIntegral_algHom_iff f hf.1).mp (hx.symm ▸ hy)
    refine ⟨⟨x, hxint⟩, ?_⟩
    funext q
    apply Subtype.ext
    exact congr_fun hx q

end integralClosure
