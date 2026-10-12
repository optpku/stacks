/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Jacobson ideals and quotient units

The canonical statements use `Ideal.jacobson ⊥`, matching Mathlib's ideal-level API. Thin
bridges to `Ring.jacobson` retain the source formulation and the interface used by existing
downstream files.

@stack 0AME
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- An ideal lies in `Ideal.jacobson ⊥` exactly when every element of `1 + I` is a unit. -/
@[stacks 0AME "ideal-level criterion"]
theorem le_jacobson_bot_iff_isUnit_one_add (I : Ideal R) :
    I ≤ jacobson (⊥ : Ideal R) ↔ ∀ f ∈ I, IsUnit (1 + f) := sorry

/-- Lemma 10.19.1 (1): an ideal lies in the ring's Jacobson radical exactly when every
element of `1 + I` is a unit. -/
@[stacks 0AME "Jacobson criterion"]
theorem le_ringJacobson_iff_isUnit_one_add (I : Ideal R) :
    I ≤ Ring.jacobson R ↔ ∀ f ∈ I, IsUnit (1 + f) := sorry

/-- Quotienting by an ideal contained in `Ideal.jacobson ⊥` reflects units. The reverse
implication is the usual preservation of units by a ring homomorphism. -/
@[stacks 0AME "quotient unit reflection"]
theorem isUnit_quotient_mk_iff_of_le_jacobson_bot
    (I : Ideal R) (hI : I ≤ jacobson (⊥ : Ideal R)) {x : R} :
    IsUnit (Ideal.Quotient.mk I x) ↔ IsUnit x := sorry

/-- Lemma 10.19.1 (2): if `I ≤ Ring.jacobson R`, every element whose image in `R ⧸ I`
is a unit is already a unit in `R`. -/
@[stacks 0AME "unit lifting"]
theorem isUnit_of_quotient_mk_of_le_ringJacobson
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) {x : R}
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := sorry

end Ideal

variable {R : Type u} [CommRing R]

/-- Compatibility entry for downstream files written before the Jacobson criterion moved into
the `Ideal` namespace. New code should use `Ideal.le_ringJacobson_iff_isUnit_one_add`. -/
theorem ideal_le_ring_jacobson_iff_isUnit_one_add (I : Ideal R) :
    I ≤ Ring.jacobson R ↔ ∀ f ∈ I, IsUnit (1 + f) := sorry
