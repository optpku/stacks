/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic

@[expose] public section

/-!
# Integral Closures as Extensions of Discrete Valuation Rings

The normalization of a DVR in a faithfully represented field extension is a
DVR extension whenever the integral closure is again a DVR.

@stack 09E8
@stack 09E9
-/

universe u v

namespace IsExtensionOfDiscreteValuationRings

section IntegralClosure

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L]

/-- The normalization map into a field extension is an extension of discrete valuation rings
when its integral closure is a discrete valuation ring. -/
@[stacks 09E9 "normalization as a DVR extension"]
instance ofIntegralClosure [FaithfulSMul A L]
    [IsDiscreteValuationRing (integralClosure A L)] :
    IsExtensionOfDiscreteValuationRings A (integralClosure A L) := sorry
-- Proof strategy: use `faithfulSMul_iff_algebraMap_injective` for injectivity and the canonical
-- local-ring structure of the integral closure DVR; prove locality of the subtype algebra map by
-- pulling units back along the integral-closure inclusion.

/-- A fraction-field tower makes the normalization map into a DVR extension whenever the
normalization is a DVR.  This explicit theorem avoids registering a second global instance next
to `ofIntegralClosure`. -/
@[stacks 09E9 "normalization DVR extension from a fraction-field tower"]
theorem ofFractionField
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [IsDiscreteValuationRing (integralClosure A L)] :
    IsExtensionOfDiscreteValuationRings A (integralClosure A L) := sorry
-- Proof strategy: obtain `FaithfulSMul A L` from injectivity of the fraction-field tower
-- `A → FractionRing A → L`, then apply the canonical `ofIntegralClosure` instance explicitly.

end IntegralClosure

end IsExtensionOfDiscreteValuationRings

namespace integralClosure

section FractionFieldFinite

variable {A : Type u} {L : Type v}
variable [CommRing A] [Field L] [Algebra A L]

/-- A finite separable extension of the fraction field gives a finite
integral closure over the base DVR. Fixing `FractionRing A` makes the field parameter inferable
for typeclass search. -/
@[stacks 09E8 "finite integral closure over a DVR"]
instance moduleFinite_of_fractionField
    [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L]
    [Algebra.IsSeparable (FractionRing A) L] :
    Module.Finite A (integralClosure A L) := sorry
-- Proof strategy: apply `IsIntegralClosure.finite A (FractionRing A) L`; the DVR supplies
-- `IsIntegrallyClosed A` and `IsNoetherianRing A`, while `integralClosure A L` supplies the
-- canonical `IsIntegralClosure` structure.

end FractionFieldFinite

end integralClosure
