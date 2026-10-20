module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import ReasLib.RingTheory.Normal.Nagata.CharZero
public import ReasLib.RingTheory.Normal.Nagata.DVR
public import ReasLib.RingTheory.Normal.Nagata.PurelyInseparable
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Nagata descent along a separable fraction-field extension

The canonical `IsN2Ring` companion and the source-facing Nagata statement are kept in this leaf;
the chapter entry is only a traceable recall.

@stack 0GLS
-/

universe u v

namespace IsExtensionOfDiscreteValuationRings

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B]
-- Local instance justification (instance diamond): install the compatible fraction-field lift
-- and scalar tower together only for this descent argument.
attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable [hAB : IsExtensionOfDiscreteValuationRings A B]
variable [hsep : Algebra.IsSeparable (FractionRing A) (FractionRing B)]

include hAB hsep

/- A reusable reformulation of the descent step; the source-facing theorem below translates it
back to the Nagata predicate using the DVR/N-2 equivalence. -/
/-- The `N-2` property descends across a separable extension of fraction fields of DVRs. -/
theorem isN2Ring_of_separable_fractionRingExtension [IsN2Ring B] :
    IsN2Ring A := sorry
-- Proof strategy: split on the characteristic of `FractionRing A`.  In characteristic zero, use
-- `IsN1Ring.iff_isN2Ring_of_fractionRingCharZero`; finiteness of the normalization over `B` follows
-- from its `N-2` property and descends to `A` through the faithfully flat DVR map.  In positive
-- characteristic, apply `IsN2Ring.iff_forall_finitePurelyInseparable`.  For a finite purely
-- inseparable `K1 / FractionRing A`, separability of `FractionRing B / FractionRing A` makes the
-- reduced tensor product a field by linear disjointness.  The `N-2` hypothesis on `B` makes its
-- integral closure finite, and faithful-flat descent of the injected tensor normalization gives
-- finiteness of the integral closure of `A` in `K1`.

/-- Lemma 15.117.2: if `A ⊆ B` is an extension of discrete valuation rings, `B` is Nagata, and
the fraction-field extension is separable, then `A` is Nagata. -/
@[stacks 0GLS "Lemma 15.117.2: Nagata descent"]
theorem nagataRing_of_separable_fractionRingExtension [NagataRing B] :
    NagataRing A := sorry
-- Proof strategy: convert the target Nagata hypothesis to `IsN2Ring B` with the DVR equivalence
-- `NagataRing.iff_isN2Ring_of_discreteValuationRing`, apply
-- `isN2Ring_of_separable_fractionRingExtension`, and convert the resulting `IsN2Ring A` back to
-- `NagataRing A` by the same equivalence.

end

end IsExtensionOfDiscreteValuationRings

end
