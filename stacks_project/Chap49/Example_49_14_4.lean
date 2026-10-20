/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Node.Different
import StacksCheckRecall

universe u

open NodeCoordinateRing

/- In arbitrary characteristic, the criterion is equality of the exponent images in `k`.
Equality of the natural exponents follows under `CharZero k`. -/

/- Example 49.14.4 -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.one_mem_complementary_cast_iff :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        ((1 : NodeCoordinateRing.GenericFiber k n m) ∈
            NodeCoordinateRing.complementary k n m ↔
          ((n : ℕ) : k) = ((m : ℕ) : k)))

/- Example 49.14.4 (1): the localized nodal power map is finite. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.localizedPowerMap_finite :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        RingHom.Finite (localizedPowerMap k n m))

/- Example 49.14.4 (2): the localized nodal power map is étale. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.localizedPowerMap_etale :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        RingHom.Etale (localizedPowerMap k n m))

/- Example 49.14.4 (3): the denominator-cleared trace of `1` is the weighted sum of the two coordinates. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.trace_one :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        genericTrace k n m (1 : GenericFiber k n m) *
            algebraMap (NodeCoordinateRing.Ring k) (FractionRing (NodeCoordinateRing.Ring k))
              (coordinate k 0 + coordinate k 1) =
          algebraMap (NodeCoordinateRing.Ring k) (FractionRing (NodeCoordinateRing.Ring k))
            (((n : ℕ) : NodeCoordinateRing.Ring k) * coordinate k 0 +
              ((m : ℕ) : NodeCoordinateRing.Ring k) * coordinate k 1))

/- Example 49.14.4 (4): traces of powers of the first coordinate vanish below the first exponent. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.trace_left_pow :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        ∀ i : ℕ, 1 ≤ i → i < (n : ℕ) →
          genericTrace k n m (genericFiberTargetMap k n m (coordinate k 0 ^ i)) = 0)

/- Example 49.14.4 (5): traces of powers of the second coordinate vanish below the second exponent. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.trace_right_pow :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        ∀ j : ℕ, 1 ≤ j → j < (m : ℕ) →
          genericTrace k n m (genericFiberTargetMap k n m (coordinate k 1 ^ j)) = 0)

/- Example 49.14.4 (6): in characteristic zero, the trace-extension criterion is equality of the natural exponents. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.one_mem_complementary_iff :
    ∀ (k : Type u) [Field k] (n m : ℕ+) [CharZero k],
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        ((1 : GenericFiber k n m) ∈ complementary k n m ↔ n = m))

/- Example 49.14.4 (7): equal exponent images give the unit complementary submodule. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.complementary_eq_one :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        ((n : ℕ) : k) = ((m : ℕ) : k) →
          complementary k n m = (1 : Submodule (NodeCoordinateRing.Ring k) (GenericFiber k n m)))

/- Example 49.14.4 (8): equal exponent images give the unit Dedekind different. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.dedekindDifferent_eq_one :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        ((n : ℕ) : k) = ((m : ℕ) : k) →
          dedekindDifferent k n m = (1 : Submodule (NodeCoordinateRing.Ring k) (GenericFiber k n m)))

/- Example 49.14.4 (9): equal exponent images give the unit target-ring ideal. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.differentIdeal_eq_top :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        ((n : ℕ) : k) = ((m : ℕ) : k) → differentIdeal k n m = ⊤)

/- Example 49.14.4 (10): a common exponent greater than one is nonflat. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.powerMap_not_flat_of_one_lt :
    ∀ (k : Type u) [Field k] (n : ℕ+),
      IsUnit (((n : ℕ) : k)) → 1 < (n : ℕ) → ¬(powerMap k n n).toRingHom.Flat)

/- Example 49.14.4 (11): a common exponent greater than one is non-unramified. -/
@[stacks 0BWP] #check
  (NodeCoordinateRing.powerMap_not_unramified_of_one_lt :
    ∀ (k : Type u) [Field k] (n : ℕ+),
      IsUnit (((n : ℕ) : k)) → 1 < (n : ℕ) → ¬(powerMap k n n).toRingHom.Unramified)

/- The finite-affine trace-lift formulation of the generalized different criterion. -/
#check
  (NodeCoordinateRing.exists_traceLift_iff :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        ((∃ t : PowerDual k n m, ∀ b : NodeCoordinateRing.Ring k,
          algebraMap (NodeCoordinateRing.Ring k) (FractionRing (NodeCoordinateRing.Ring k)) (t b) =
            genericTrace k n m (genericFiberTargetMap k n m b)) ↔
          ((n : ℕ) : k) = ((m : ℕ) : k)))

/- The trace lift generates the finite-affine dual in the unit-different case. -/
#check
  (NodeCoordinateRing.traceLift_generates_dual :
    ∀ (k : Type u) [Field k] (n m : ℕ+),
      IsUnit (((n : ℕ) : k)) → IsUnit (((m : ℕ) : k)) →
        ((n : ℕ) : k) = ((m : ℕ) : k) → ∀ t : PowerDual k n m,
          (∀ b : NodeCoordinateRing.Ring k,
            algebraMap (NodeCoordinateRing.Ring k) (FractionRing (NodeCoordinateRing.Ring k)) (t b) =
              genericTrace k n m (genericFiberTargetMap k n m b)) →
          ∀ φ : PowerDual k n m, ∃ b : NodeCoordinateRing.Ring k,
            ∀ c : NodeCoordinateRing.Ring k, φ c = t (b * c))

/- The same common-exponent counterexample is also non-étale. -/
#check
  (NodeCoordinateRing.powerMap_not_etale_of_one_lt :
    ∀ (k : Type u) [Field k] (n : ℕ+),
      IsUnit (((n : ℕ) : k)) → 1 < (n : ℕ) → ¬RingHom.Etale (powerMap k n n).toRingHom)
