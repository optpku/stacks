/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Valuation.Extension.Finite
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Residue
public import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite extensions of discrete valuation rings

This leaf owns the finite-residue and `e * f` comparison statements for an extension of
discrete valuation rings. The valuation-ring inequality remains in
`ReasLib.RingTheory.Valuation.Extension.Finite`; this file supplies the DVR-facing specialization
and the small value-group bridges used by the height-one localization files.

@stack 09E5
-/

universe u v

open Ideal IsLocalRing

-- Local instance justification (defeq pin): use the canonical fraction-field algebra and scalar
-- tower only while specializing the valuation-ring statements to the DVR fraction fields.
attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

namespace IsExtensionOfDiscreteValuationRings

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

local notation "K[A]" => FractionRing A
local notation "K[B]" => FractionRing B

/-- Lemma 15.112.2 (09E5; current Stacks Lemma 15.113.2), finite residue-field clause: a finite
fraction-field extension induces a finite-dimensional extension of residue fields. -/
@[stacks 09E5 "finite residue-field extension"]
instance finiteDimensional_residueField_of_finiteDimensional_fractionField_extension
    [FiniteDimensional K[A] K[B]] :
    FiniteDimensional (ResidueField A) (ResidueField B) := sorry
-- Proof strategy: specialize
-- `IsExtensionOfValuationRings.finiteDimensional_residueField` to the canonical valuation-ring
-- structures on `A` and `B`, using the pinned fraction-field algebra and scalar tower above.

/-- The value-group ramification index of the valuation-ring owner dominates the DVR ramification
index. This is the comparison needed by height-one localization consumers. -/
@[stacks 09E5 "comparison with the valuation-ring ramification index"]
theorem valuationRing_ramificationIndex_le :
    (IsExtensionOfDiscreteValuationRings.ramificationIndex A B : ℕ∞) ≤
      IsExtensionOfValuationRings.ramificationIndex A B := sorry
-- Proof strategy: identify the DVR ramification index with the exponent by which the source
-- value-group generator maps to the target generator, then compare the resulting cyclic subgroup
-- index with `IsExtensionOfValuationRings.ramificationIndex`.

/-- For an extension of discrete valuation rings, the ramification-index definition of weak
unramifiedness (09E4) agrees with the value-group definition (0ASG). The valuation-ring structures
and extension instance are inferred from the DVR structures and extension. No finiteness of the
fraction-field extension is required. -/
@[stacks 09E4 "comparison with valuation-ring weak unramifiedness (0ASG)"]
theorem weaklyUnramified_iff_valuationRing
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] :
    IsExtensionOfDiscreteValuationRings.WeaklyUnramified A B ↔
      IsExtensionOfValuationRings.WeaklyUnramified A B := sorry
-- Proof strategy: with uniformizer generators, the map of value groups is multiplication by the
-- positive DVR ramification index. It is bijective exactly when this index is one; adjoining zero
-- preserves this criterion.

/-- Lemma 15.112.2 (09E5; current Stacks Lemma 15.113.2), `e * f` clause: the DVR ramification
index times the residue degree is bounded by the fraction-field dimension. -/
@[stacks 09E5 "ramification index times residue degree"]
theorem ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension
    [FiniteDimensional K[A] K[B]] :
    IsExtensionOfDiscreteValuationRings.ramificationIndex A B *
        IsExtensionOfDiscreteValuationRings.residueDegree A B ≤
      Module.finrank K[A] K[B] := sorry
-- Proof strategy: start from
-- `IsExtensionOfValuationRings.ramificationIndex_mul_residueDegree_le_finrank`, rewrite the
-- valuation residue degree using `residueDegree_eq_finrank`, apply
-- `valuationRing_ramificationIndex_le`, and eliminate `⊤` from the finite `ℕ∞` quantities before
-- casting the inequality back to `ℕ`.

end

end IsExtensionOfDiscreteValuationRings

/- The following root-level bridges retain the argument shape consumed by the localization files.
They are mathematical value-group/unit statements, not chapter-local data owners. -/

/-- A unit in the target value-group subgroup comes from a unit of the source value group. -/
@[stacks 09E5 "value-group unit preimage"]
lemma exists_source_value_group_unit_of_mem_valueGroup
    {A : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
    {γ : (ValuativeRel.ValueGroupWithZero (FractionRing B))ˣ}
    (hγ : γ ∈ MonoidWithZeroHom.valueGroup
      (ValuativeExtension.mapValueGroupWithZero (FractionRing A) (FractionRing B))) :
    ∃ δ : (ValuativeRel.ValueGroupWithZero (FractionRing A))ˣ,
      Units.map
        (ValuativeExtension.mapValueGroupWithZero (FractionRing A) (FractionRing B)).toMonoidHom δ =
        γ := sorry
-- Proof strategy: unfold `MonoidWithZeroHom.valueGroup` as the range of the induced map on units,
-- extract a source unit from `hγ`, and use `Units.ext` to turn the range equality into the stated
-- equality of units.

/-- An element of valuation one in a DVR fraction field is the image of a ring unit. -/
@[stacks 09E5 "valuation-one fraction-field element comes from a ring unit"]
lemma target_ring_unit_of_valuation_eq_one
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
    {z : FractionRing B}
    (hz : (ValuativeRel.valuation (FractionRing B)) z = 1) :
    ∃ w : Bˣ, algebraMap B (FractionRing B) (w : B) = z := sorry
-- Proof strategy: identify `B` with the integer ring of its canonical discrete valuation on
-- `FractionRing B`, apply `Valuation.Integers.isUnit_iff_valuation_eq_one` to `hz`, and transport
-- the resulting unit through the canonical fraction-ring algebra map.
