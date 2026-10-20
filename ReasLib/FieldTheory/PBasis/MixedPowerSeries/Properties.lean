/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ZMod
public import ReasLib.FieldTheory.PBasis
public import ReasLib.FieldTheory.PBasis.MixedPowerSeries
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Properties of mixed power-series rings attached to a p-basis

This leaf owns the domain, characteristic, intersection, directedness, and finiteness properties
of the explicit mixed-power construction from `FieldExtension.PBasis.MixedPowerSeries`.

@stack 07P5
-/

@[expose] public section

noncomputable section

universe u v w z

namespace FieldExtension.PBasis

namespace mixedPowerSeriesPolynomialRing

/-- A mixed power-series/polynomial ring over a field is a domain. -/
@[stacks 07P5 "mixed ring domain"]
instance isDomain {σ : Type v} {τ : Type w} [Finite σ] [Finite τ]
    (k : Type u) [Field k] : IsDomain (mixedPowerSeriesPolynomialRing σ τ k) := sorry

/-- The fraction field of a mixed ring has the characteristic of its coefficient field. -/
@[stacks 07P5 "mixed fraction-field characteristic"]
instance fractionRingCharP {p : ℕ} {σ : Type v} {τ : Type w}
    [Finite σ] [Finite τ] (k : Type u) [Field k] [CharP k p] :
    CharP (FractionRing (mixedPowerSeriesPolynomialRing σ τ k)) p := sorry

end mixedPowerSeriesPolynomialRing

namespace pthPowerMixedSubringModel

/-- The fresh-variable presentation of a mixed p-power subring is a domain. -/
@[stacks 07P5 "mixed p-power model domain"]
instance isDomain (σ : Type v) (τ : Type w) {p : ℕ} [Fact p.Prime]
    [Finite σ] [Finite τ] {ι : Type z} [DecidableEq ι]
    (k : Type u) [Field k] [CharP k p] (x : ι → k) (J : Finset ι) :
    IsDomain (pthPowerMixedSubringModel σ τ k x J) := sorry

end pthPowerMixedSubringModel

namespace pthPowerMixedSubring

variable {p : ℕ} [Fact p.Prime] {ι : Type z} [DecidableEq ι]
variable {σ : Type v} [Finite σ] {τ : Type w} [Finite τ]
variable (k : Type u) [Field k] [CharP k p]
variable (x : ι → k)

section Basis

variable [Algebra (ZMod p) k]

/-- Lemma 15.46.5 (1): for a p-basis of `k` over `ZMod p`, the intersection of the mixed
fraction subfields is the Frobenius subfield of the ambient fraction field. -/
@[stacks 07P5 "intersection of mixed fraction subfields"]
theorem fractionSubfield_iInf_eq_frobenius
    (hx : IsBasis p (ZMod p) x) :
    (⨅ J : Finset ι, pthPowerMixedFractionSubfield σ τ k x J) =
      FieldExtension.Frobenius.subfield p
        (FractionRing (mixedPowerSeriesPolynomialRing σ τ k)) := sorry

end Basis

/-- Lemma 15.46.5 (2): the mixed fraction subfields form a downward directed family. -/
@[stacks 07P5 "directed mixed fraction subfields"]
theorem fractionSubfield_directed :
    Directed (· ≥ ·) fun J : Finset ι ↦ pthPowerMixedFractionSubfield σ τ k x J := sorry

section Basis

variable [Algebra (ZMod p) k]

/-- Lemma 15.46.5 (3): the ambient mixed ring is finite over every intrinsic mixed p-power
subring attached to a finite set of p-basis indices. -/
@[stacks 07P5 "finite mixed p-power extension"]
theorem moduleFinite (hx : IsBasis p (ZMod p) x) (J : Finset ι) :
    Module.Finite (pthPowerMixedSubring σ τ k x J)
      (mixedPowerSeriesPolynomialRing σ τ k) := sorry

end Basis

end pthPowerMixedSubring

end FieldExtension.PBasis
