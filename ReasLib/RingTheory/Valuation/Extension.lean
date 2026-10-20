/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.SetTheory.Cardinal.ENat
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Extensions of valuation rings

This leaf owns the valuation-ring extension interface. The extension class is
the injective local algebra map; the fraction-field valuation relation and its
value-group map are canonical derived instances. The weakly-unramified
predicate, residue degree, and ramification index are kept in the same
namespace so downstream users can import this file directly.
-/

universe u v

open IsLocalRing Valuation

/-- An extension of valuation rings is an injective local algebra map `A → B`. -/
@[stacks 0ASG "Definition 15.124.1 (1), extension of valuation rings"]
class IsExtensionOfValuationRings (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [ValuationRing A] [IsDomain B] [ValuationRing B] : Prop
    extends IsLocalHom (algebraMap A B) where
  /-- The structure map of an extension of valuation rings is injective. -/
  algebraMap_injective : Function.Injective (algebraMap A B)

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]

/-- The identity map of a valuation ring is an extension of valuation rings. -/
@[stacks 0ASG "identity extension of a valuation ring", instance]
instance valuationRingSelfExtension : IsExtensionOfValuationRings A A := sorry
-- Proof strategy: use `isLocalHom_id A` for locality and the injectivity of the
-- identity algebra map for `algebraMap_injective`.

end

/-- The extension class is equivalent to locality together with injectivity of the structure
map. -/
@[stacks 0ASG "Definition 15.124.1 (1), local-injective criterion"]
theorem isExtensionOfValuationRings_iff
    (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [ValuationRing A] [IsDomain B] [ValuationRing B] :
    IsExtensionOfValuationRings A B ↔
      IsLocalHom (algebraMap A B) ∧ Function.Injective (algebraMap A B) := sorry
-- Proof strategy: project the two fields of `IsExtensionOfValuationRings` in
-- the forward direction and invoke its constructor on the pair in the reverse
-- direction.

namespace IsExtensionOfValuationRings

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [ValuationRing A] [IsDomain B] [ValuationRing B]
variable [h : IsExtensionOfValuationRings A B]

-- Local declaration justification (source-local notation): the formulas below compare the
-- source valuation ring with its fraction field.
local notation "K" => FractionRing A
-- Local declaration justification (source-local notation): the formulas below compare the
-- target valuation ring with its fraction field.
local notation "L" => FractionRing B
-- Local declaration justification (source-local notation): the ramification formula uses the
-- target fraction field's value group with zero repeatedly.
local notation "ΓL" => ValuativeRel.ValueGroupWithZero L
-- Local declaration justification (source-local notation): the extension formulas distinguish
-- the canonical valuation on the source fraction field.
local notation "vA" => ValuationRing.valuation A K
-- Local declaration justification (source-local notation): the extension formulas distinguish
-- the canonical valuation on the target fraction field.
local notation "vB" => ValuationRing.valuation B L

include h
/-- The `A`-action on `B` is faithful because the extension map is injective. -/
@[stacks 0ASG "faithful scalar action of a valuation-ring extension", instance]
instance faithfulSMul : FaithfulSMul A B :=
  (faithfulSMul_iff_algebraMap_injective A B).mpr h.algebraMap_injective

-- Local instance justification (instance diamond): the fraction-field algebra is canonical but
-- intentionally installed only while defining the induced valuation extension.
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

include h
/-- The valuation integers of the target fraction field pull back to those of the source. -/
@[stacks 0ASG "fraction-field valuation integers under an extension"]
theorem integer_comap :
    Subring.comap (algebraMap K L) (Valuation.integer vB) = Valuation.integer vA := sorry
-- Proof strategy: ext a source fraction `x`.  The forward implication uses the
-- valuation-ring alternative for `x` and `x⁻¹`; in the inverse branch, locality
-- of `A → B` reflects the target unit back to a source unit.  The reverse
-- implication maps an integer representative from `A` into `B`.

/-- The source fraction field carries the valuation relation induced by its valuation ring. -/
@[stacks 0ASG "valuative relation on the source fraction field", instance]
noncomputable instance fractionRingValuativeRel_source : ValuativeRel K :=
  ValuativeRel.ofValuation vA

/-- The target fraction field carries the valuation relation induced by its valuation ring. -/
@[stacks 0ASG "valuative relation on the target fraction field", instance]
noncomputable instance fractionRingValuativeRel_target : ValuativeRel L :=
  ValuativeRel.ofValuation vB

/-- The source valuation is compatible with its induced valuative relation. -/
@[stacks 0ASG "compatibility of the source fraction-field valuation", instance]
instance fractionRing_valuation_compatible_source : Valuation.Compatible vA := sorry
-- Proof strategy: apply `Valuation.Compatible.ofValuation vA` to the valuative
-- relation installed by `fractionRingValuativeRel_source`.

/-- The target valuation is compatible with its induced valuative relation. -/
@[stacks 0ASG "compatibility of the target fraction-field valuation", instance]
instance fractionRing_valuation_compatible_target : Valuation.Compatible vB := sorry
-- Proof strategy: apply `Valuation.Compatible.ofValuation vB` to the valuative
-- relation installed by `fractionRingValuativeRel_target`.

include h
/-- The fraction-field algebra map extends the source valuation to the target valuation. -/
@[stacks 0ASG "extension of the source valuation to the target fraction field", instance]
instance fractionRing_hasExtension : Valuation.HasExtension vA vB :=
  Valuation.HasExtension.ofComapInteger (integer_comap A B)

include h
/-- The fraction-field extension is a valuative extension. -/
@[stacks 0ASG "canonical valuative extension of fraction fields"]
theorem fractionRingValuativeExtension_spec : ValuativeExtension K L := sorry
-- Proof strategy: construct the Prop-valued class, rewrite both valuative
-- relations with `Valuation.vle_iff_le`, and use
-- `Valuation.HasExtension.val_map_le_iff` from `integer_comap`.

/-- The canonical valuative extension of the fraction fields of an extension of valuation rings. -/
@[stacks 0ASG "valuative extension on fraction fields", instance]
instance fractionRingValuativeExtension : ValuativeExtension K L :=
  fractionRingValuativeExtension_spec A B

/-- An extension `A ⊆ B` of valuation rings is weakly unramified when the induced map of value
groups with zero is bijective. -/
@[stacks 0ASG "Definition 15.124.1 (2), weakly unramified"]
def WeaklyUnramified : Prop :=
  Function.Bijective (ValuativeExtension.mapValueGroupWithZero K L)

/-- The defining value-group criterion for a weakly unramified extension. -/
theorem WeaklyUnramified.spec (hWeak : WeaklyUnramified A B) :
    Function.Bijective (ValuativeExtension.mapValueGroupWithZero K L) := sorry
-- Proof strategy: unfold `WeaklyUnramified`; the conclusion is its defining
-- proposition.

/-- When the residue-field extension is finite, its residue degree is the vector-space dimension
`[κ_B : κ_A]`. -/
@[stacks 0ASG "Definition 15.124.1 (3), residue degree"]
noncomputable def residueDegree [FiniteDimensional (ResidueField A) (ResidueField B)] : ℕ :=
  Module.finrank (ResidueField A) (ResidueField B)

/-- The ramification index is the cardinality of the target value-group quotient by the image of
the induced value-group map. -/
@[stacks 0ASG "ramification index of a valuation-ring extension"]
noncomputable def ramificationIndex : ℕ∞ :=
  ENat.card
    (ΓLˣ ⧸ MonoidWithZeroHom.valueGroup (ValuativeExtension.mapValueGroupWithZero K L))

/-- The ramification index of an extension of valuation rings is positive. -/
@[stacks 0ASG "positivity of the ramification index"]
theorem ramificationIndex_pos : 0 < ramificationIndex A B := sorry
-- Proof strategy: unfold `ramificationIndex`; the quotient group is nonempty,
-- so its extended-natural cardinality is positive (`ENat.card_pos`).

end IsExtensionOfValuationRings

/-- A fraction-field model carries the canonical faithful action of the base ring.  This is a
   reusable support instance for normalization statements; the fraction field is fixed to
   `FractionRing A`, so typeclass search has no ambiguous model parameter. -/
@[stacks 0ASG "fraction-field faithful support"]
noncomputable instance fractionRing_faithfulSMul
    {A : Type u} {L : Type v} [CommRing A] [IsDomain A] [Field L]
    [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] : FaithfulSMul A L :=
  FaithfulSMul.of_field_isFractionRing A L (FractionRing A) L

section IntegralClosure

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [ValuationRing A]
variable [Field L] [Algebra A L] [hFaithful : FaithfulSMul A L]

include hFaithful
/-- The normalization map is injective when the original action on `L` is faithful. -/
theorem integralClosure_algebraMap_injective :
    Function.Injective (algebraMap A (integralClosure A L)) := sorry
-- Proof strategy: compose with the canonical inclusion of the integral closure
-- into `L`, rewrite the composite by `IsScalarTower.algebraMap_eq`, and apply
-- `FaithfulSMul.algebraMap_injective A L`.

/-- The integral normalization map between valuation rings is local. -/
@[stacks 0ASG "locality of the normalization map between valuation rings"]
theorem integralClosure_isLocalHom [ValuationRing (integralClosure A L)] :
    IsLocalHom (algebraMap A (integralClosure A L)) := sorry
-- Proof strategy: use integrality of the normalization map together with
-- `integralClosure_algebraMap_injective`, then apply the canonical theorem that
-- an injective integral map between valuation rings is local.

/-- The normalization map is an extension of valuation rings when the normalization is a valuation
ring. -/
@[stacks 0ASG "valuation-ring extension to the integral closure", instance]
instance integralClosure_extension [ValuationRing (integralClosure A L)] :
    IsExtensionOfValuationRings A (integralClosure A L) where
  toIsLocalHom := integralClosure_isLocalHom (A := A) (L := L)
  algebraMap_injective := integralClosure_algebraMap_injective (A := A) (L := L)

end IntegralClosure

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B]
variable [h : IsExtensionOfDiscreteValuationRings A B]

include h
/-- A discrete-valuation-ring extension is canonically an extension of valuation rings. -/
@[stacks 0ASG "discrete valuation extension as a valuation-ring extension", instance]
instance discreteValuationRingExtension_toIsExtensionOfValuationRings :
    IsExtensionOfValuationRings A B where
  toIsLocalHom := h.toIsLocalHom
  algebraMap_injective := h.algebraMap_injective

end
