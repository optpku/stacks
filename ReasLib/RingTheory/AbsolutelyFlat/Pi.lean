/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AbsolutelyFlat

/-!
# Products of absolutely flat rings

This leaf records the product-of-fields specialization of the general
dependent-product instance for absolutely flat rings.

@stack 092G
-/

@[expose] public section

universe u v

variable {ι : Type u} (K : ι → Type v) [∀ i, Field (K i)]

/-- A dependent product of fields is an absolutely flat ring. -/
@[stacks 092G "products of fields are absolutely flat"]
theorem isAbsolutelyFlatRing_pi : IsAbsolutelyFlatRing ((i : ι) → K i) := sorry
