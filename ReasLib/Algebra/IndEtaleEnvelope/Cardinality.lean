/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import ReasLib.Algebra.IndEtaleEnvelope.Iteration

/-!
# Cardinality bounds for ind-étale envelopes

The finite stages, their indexing set, the ind-étale envelope, and its
sequential iteration are bounded by any infinite cardinal bounding the base
ring.
-/

@[expose] public section

universe u

open scoped Cardinal

namespace Algebra.IndEtaleEnvelope

/-- The standard-smooth presentations of a commutative ring have cardinality
at most any infinite cardinal bounding the ring. -/
theorem mk_presentation_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    #(Presentation A) ≤ κ :=
  sorry

/-- The finite-subset index of the standard-smooth presentations has
cardinality at most any infinite cardinal bounding the ring. -/
theorem mk_index_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    #(Index A) ≤ κ :=
  sorry

/-- Every finite stage of the ind-étale envelope has cardinality at most any
infinite cardinal bounding the base ring. -/
theorem mk_stage_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) (E : Index A) :
    #(stage E) ≤ κ :=
  sorry

/-- The ind-étale envelope has cardinality at most the maximum of the base
ring cardinality and the countable cardinal. -/
theorem mk_le_max (A : Type u) [CommRing A] :
    #(IndEtaleEnvelope A) ≤ #A ⊔ ℵ₀ :=
  sorry

/-- The ind-étale envelope has cardinality at most any infinite cardinal
bounding the base ring. -/
theorem mk_le (A : Type u) [CommRing A] {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (hA : #A ≤ κ) :
    #(IndEtaleEnvelope A) ≤ κ :=
  sorry

/-- Every iterate of the ind-étale envelope has cardinality at most any
infinite cardinal bounding the base ring. -/
theorem mk_iterate_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) (n : ℕ) :
    #(iterate A n) ≤ κ :=
  sorry

/-- The sequential colimit of the iterated envelopes has cardinality at most
the maximum of the base ring cardinality and the countable cardinal. -/
theorem mk_iteration_le_max (A : Type u) [CommRing A] :
    #(Iteration A) ≤ #A ⊔ ℵ₀ :=
  sorry

/-- The sequential colimit of the iterated envelopes has cardinality at most
any infinite cardinal bounding the base ring. -/
theorem mk_iteration_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    #(Iteration A) ≤ κ :=
  sorry

end Algebra.IndEtaleEnvelope
