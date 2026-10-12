/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Extensions of Discrete Valuation Rings

This file owns the basic predicate for an injective local map between discrete
valuation rings. Ramification and residue-field invariants live in sibling
modules so that consumers can import only the layer they use.
-/

universe u v w

/-- An extension of discrete valuation rings is an injective local algebra map. -/
@[stacks 09E4 "DVR extension"]
class IsExtensionOfDiscreteValuationRings (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B] : Prop
    extends IsLocalHom (algebraMap A B) where
  /-- The algebra map of an extension of discrete valuation rings is injective. -/
  algebraMap_injective : Function.Injective (algebraMap A B)

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- The identity map of a discrete valuation ring is an extension of discrete valuation rings. -/
instance IsExtensionOfDiscreteValuationRings.instSelf :
    IsExtensionOfDiscreteValuationRings A A := sorry
-- Proof strategy: construct the class with the canonical local-hom instance for
-- `algebraMap A A` and `Function.injective_id`, simplifying the identity algebra map where
-- necessary.

end

/-- An extension of discrete valuation rings is equivalently an injective local algebra map. -/
theorem isExtensionOfDiscreteValuationRings_iff
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B] :
    IsExtensionOfDiscreteValuationRings A B ↔
      IsLocalHom (algebraMap A B) ∧ Function.Injective (algebraMap A B) := sorry
-- Proof strategy: in the forward direction project `toIsLocalHom` and
-- `algebraMap_injective`; in the reverse direction construct
-- `IsExtensionOfDiscreteValuationRings` from the two hypotheses.

namespace IsExtensionOfDiscreteValuationRings

/-- A tower of extensions of discrete valuation rings induces an extension on the composite map. -/
theorem of_tower
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsExtensionOfDiscreteValuationRings A B] [IsExtensionOfDiscreteValuationRings B C] :
    IsExtensionOfDiscreteValuationRings A C := sorry
-- Proof strategy: compose the two `IsLocalHom` structures, rewrite their ring-hom composition
-- as `algebraMap A C` with `IsScalarTower.algebraMap_eq`, and compose the two injectivity fields.

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B]

/-- The scalar action of the base DVR on an extension DVR is faithful. -/
instance instFaithfulSMul [IsExtensionOfDiscreteValuationRings A B] : FaithfulSMul A B := sorry
-- Proof strategy: apply `faithfulSMul_iff_algebraMap_injective` and use
-- `IsExtensionOfDiscreteValuationRings.algebraMap_injective`.

end

end IsExtensionOfDiscreteValuationRings
