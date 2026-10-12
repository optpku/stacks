/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import ReasLib.RingTheory.Valuation.Extension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Purely inseparable extensions of valuation rings

@stack 0H37

The integral-closure valuation-ring statement is kept as a valuation-ring
owner.  Its fraction-field statement is exposed as a named theorem and a
canonical instance; the instance has the purely inseparable hypotheses in its
term, so they cannot be silently pruned by a `sorry` body.
-/

universe u v

open IsLocalRing Valuation

namespace integralClosure

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [ValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [IsPurelyInseparable (FractionRing A) L]

/-- Lemma 15.124.3 (2): the integral closure in a purely inseparable fraction-field extension has
fraction field `L`. -/
@[stacks 0H37 "Lemma 15.124.3 (2), fraction field of the normalization"]
theorem isFractionRing_of_purelyInseparable :
    IsFractionRing (integralClosure A L) L := sorry
-- Proof strategy: purely inseparable implies algebraic over `FractionRing A`.
-- Apply `integralClosure.isFractionRing_of_algebraic`, discharging injectivity
-- of `A → L` with the canonical faithful action from the fraction-field tower.

/-- The fraction-field statement is available to typeclass search in the canonical
`FractionRing A` model. -/
@[stacks 0H37 "Lemma 15.124.3 (2), canonical fraction-ring instance"]
noncomputable instance fractionRing_of_purelyInseparable :
    IsFractionRing (integralClosure A L) L :=
  isFractionRing_of_purelyInseparable (A := A) (L := L)

end integralClosure

namespace ValuationRing

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [ValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [IsPurelyInseparable (FractionRing A) L]

/-- Lemma 15.124.3 (1): the integral closure in a purely inseparable extension is a valuation ring.
-/
@[stacks 0H37 "Lemma 15.124.3 (1), valuation ring of the normalization"]
theorem integralClosure_of_purelyInseparable :
    ValuationRing (integralClosure A L) := sorry
-- Proof strategy: use the valuation-ring criterion inside the fraction field
-- `L`.  For `x : L`, a purely inseparable power lies in `FractionRing A`; the
-- valuation-ring alternative there makes either that power or its inverse come
-- from `A`.  Integrality descends from a positive power, so either `x` or `x⁻¹`
-- belongs to the integral closure.

end ValuationRing

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [ValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [IsPurelyInseparable (FractionRing A) L]

/-- Lemma 15.124.3 (1): install the valuation-ring structure on the normalization. -/
@[stacks 0H37 "Lemma 15.124.3 (1), canonical valuation-ring instance"]
instance integralClosure_valuationRing_of_purelyInseparable :
    ValuationRing (integralClosure A L) :=
  ValuationRing.integralClosure_of_purelyInseparable (A := A) (L := L)

/-- Lemma 15.124.3 (3): the normalization inclusion is an extension of valuation rings. -/
@[stacks 0H37 "Lemma 15.124.3 (3), normalization extension"]
theorem integralClosure_extension_of_purelyInseparable :
    IsExtensionOfValuationRings A (integralClosure A L) := sorry
-- Proof strategy: install the preceding valuation-ring and fraction-ring
-- instances, synthesize the canonical faithful `A`-action on `L`, and apply
-- `integralClosure_extension` from the base extension owner.
