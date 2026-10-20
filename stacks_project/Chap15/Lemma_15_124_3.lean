/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Valuation.Extension.PurelyInseparable
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.124.3

@stack 0H37

This file is a thin source-facing recall.  The valuation-ring, fraction-field,
and extension statements are owned by the valuation extension leaf, so no
chapter-local normalization instance or purely inseparable proof is repeated.
-/

-- Lemma 15.124.3 (1): the normalization is a valuation ring.
@[stacks 0H37 "Lemma 15.124.3 (1), valuation ring of the normalization"]
#check @ValuationRing.integralClosure_of_purelyInseparable

-- Lemma 15.124.3 (2): the normalization has fraction field `L`.
@[stacks 0H37 "Lemma 15.124.3 (2), fraction field of the normalization"]
#check @integralClosure.isFractionRing_of_purelyInseparable
#check @integralClosure.fractionRing_of_purelyInseparable

-- Lemma 15.124.3 (3): the normalization inclusion is an extension of valuation rings.
@[stacks 0H37 "Lemma 15.124.3 (3), normalization extension"]
#check @integralClosure_extension_of_purelyInseparable

section

universe u v

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [IsPurelyInseparable (FractionRing A) L]

#synth ValuationRing (integralClosure A L)
#synth IsFractionRing (integralClosure A L) L
#synth IsExtensionOfValuationRings A (integralClosure A L)

end
