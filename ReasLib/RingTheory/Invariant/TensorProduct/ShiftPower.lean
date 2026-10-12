/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Invariant.TensorProduct
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.RingTheory.RingHom.ShiftPower

@[expose] public section

/-!
# Shift-power consequences for invariant tensor maps

The orbit-polynomial and kernel identities are kept in the smaller tensor-product invariant
leaf.  This sibling adds the generation, integrality, and locally-nilpotent-kernel views used by
later downstream arguments.

@stack 0BRH
-/

open Algebra.TensorProduct.RightAction
open scoped TensorProduct Algebra.TensorProduct.RightAction

universe u v w x

namespace Algebra.IsInvariant.TensorProduct

variable {S : Type u} {A : Type v} {B : Type w} {G : Type x}
variable [CommRing S] [CommRing A] [CommRing B]
variable [Algebra S A] [Algebra S B]
variable [Group G] [MulSemiringAction G B] [SMulCommClass G S B]
variable [Finite G] [Algebra.IsInvariant S B G]

/-- The canonical map to fixed tensors is shift-power generated. -/
@[stacks 0BRH "fixed tensor map is shift-power generated"]
theorem isGenerated :
    RingHom.ShiftPower.IsGenerated
      (toFixed (S := S) (A := A) (B := B) (G := G)).toRingHom := sorry
-- Proof strategy: use `RingHom.ShiftPower.isGenerated_iff_adjoin_top` and prove top membership
-- elementwise.  For each fixed tensor `b`, `exists_monic b` gives exponent `Nat.card G`, positive
-- by `Nat.card_pos`, and the required shifted-power equation; hence `b` lies in the canonical
-- generator set and therefore in its adjoin.

/-- The canonical map to fixed tensors is integral. -/
@[stacks 0BRH "integrality of the fixed tensor map"]
theorem isIntegral :
    (toFixed (S := S) (A := A) (B := B) (G := G)).toRingHom.IsIntegral := sorry
-- Proof strategy: apply `RingHom.ShiftPower.isIntegral` to `isGenerated`.

variable [FaithfulSMul S B]

/-- The kernel of the fixed-tensor map is locally nilpotent. -/
@[stacks 0BRH "locally nilpotent kernel of the fixed tensor map"]
theorem ker_isLocallyNilpotent :
    (RingHom.ker (toFixed (S := S) (A := A) (B := B) (G := G)).toRingHom).IsLocallyNilpotent := sorry
-- Proof strategy: use `Ideal.isLocallyNilpotent_iff`.  For a kernel element, apply `kernel_pow`
-- and compare constant coefficients, equivalently evaluate the polynomial identity at zero, to
-- obtain `(-a) ^ Nat.card G = 0`.  Since `Nat.card_pos`, this makes `a` nilpotent.

end Algebra.IsInvariant.TensorProduct
