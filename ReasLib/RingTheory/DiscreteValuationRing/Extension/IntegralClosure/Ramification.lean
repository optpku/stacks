/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.IntegralClosure
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ramification of integral closures over a DVR

The source degree formula is expressed with Mathlib's modern prime-over API.  A prime `Q` of the
integral closure carries its ramification index and inertia degree as `Q.ramificationIdx A` and
`Q.inertiaDeg A`; the base prime is recovered canonically as `Q.under A`.

@stack 09E8
-/

open Ideal IsLocalRing
open scoped BigOperators

universe u v

namespace integralClosure.Ramification

/-- The maximal branches of a finite fraction-field normalization form a canonical finite type.
The torsion-free pins are the standard fraction-field transport used by the Dedekind prime-fiber
owner; they are kept inside this instance so no competing module structure is exported. -/
@[stacks 09E8 "finite maximal branches of a normalized DVR extension"]
noncomputable instance finitePrimesOver
    {A : Type u} {L : Type v}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L]
    [Algebra.IsSeparable (FractionRing A) L] :
    Fintype ((maximalIdeal A).primesOver (integralClosure A L)) :=
  -- Local instance justification (proof-local temporary data): transport the canonical
  -- fraction-field torsion-free structure to the base DVR while constructing the finite fiber.
  letI : Module.IsTorsionFree A L :=
    Module.IsTorsionFree.trans_faithfulSMul A (FractionRing A) L
  -- Local instance justification (proof-local temporary data): the integral closure inherits
  -- torsion-freeness from the ambient field, as required by the Dedekind prime-fiber owner.
  letI : Module.IsTorsionFree A (integralClosure A L) :=
    IsIntegralClosure.isTorsionFree A L
  Set.Finite.fintype
    (IsDedekindDomain.primesOver_finite (maximalIdeal A) (integralClosure A L))

/-- Remark 15.112.6 (3): for a finite separable extension of the fraction field of a DVR, its
degree is the sum of ramification indices times inertia degrees over the maximal ideal. -/
@[stacks 09E8 "integral-closure ramification-inertia formula"]
theorem finrank_eq_sum
    {A : Type u} {L : Type v}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L]
    [Algebra.IsSeparable (FractionRing A) L] :
    Module.finrank (FractionRing A) L =
      ∑ Q : (maximalIdeal A).primesOver (integralClosure A L),
        Q.1.ramificationIdx A * Q.1.inertiaDeg A := sorry
-- Proof strategy: apply `Ideal.sum_ramification_inertia_eq_finrank` to `maximalIdeal A` and
-- `integralClosure A L`; use `integralClosure.moduleFinite_of_fractionField`, torsion-freeness over
-- the DVR for `Module.Flat`, and `finitePrimesOver`, then identify the integral-closure finrank
-- with `Module.finrank (FractionRing A) L` using the fraction-field normalization theorem.

end integralClosure.Ramification
