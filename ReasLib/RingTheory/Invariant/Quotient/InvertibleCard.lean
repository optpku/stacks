/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.FixedPoints.Exact
public import ReasLib.RingTheory.Invariant.Quotient

@[expose] public section

/-!
# Fixed points of stable quotients when the group order is invertible

This leaf specializes exactness of fixed points to stable ideal quotients. Injectivity is already
available without finiteness as `Ideal.Quotient.FixedPoints.map_injective`; this file supplies the
finite-group surjectivity and bijectivity statements.
@stack 0H36
-/

universe u v

namespace Ideal.Quotient.FixedPoints

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R]
variable [Finite G]

/-- The fixed-point quotient map is surjective when the order of the acting group is a unit. -/
@[stacks 0H36 "surjectivity for fixed points of a stable quotient"]
theorem map_surjective_of_isUnit_card (I : Ideal R) (hI : I.IsStable G)
    (h_card : IsUnit (Nat.card G : R)) :
    Function.Surjective (Ideal.Quotient.fixedPointsMap I hI) := sorry
-- Proof strategy: apply `MulSemiringActionHom.fixedPoints_surjective_of_isUnit_card` to the
-- equivariant quotient projection `Ideal.Quotient.mkHom I hI`; its underlying quotient map is
-- surjective by `Ideal.Quotient.mk_surjective`.  Keep the quotient action pinned to the proof
-- `hI` while identifying the induced fixed-point map with `fixedPointsMap I hI`.

/-- The fixed-point quotient map is bijective when the order of the acting group is a unit. -/
@[stacks 0H36 "bijectivity for fixed points of a stable quotient"]
theorem map_bijective_of_isUnit_card (I : Ideal R) (hI : I.IsStable G)
    (h_card : IsUnit (Nat.card G : R)) :
    Function.Bijective (Ideal.Quotient.fixedPointsMap I hI) := sorry
-- Proof strategy: pair the unconditional injectivity theorem `map_injective I hI` with
-- `map_surjective_of_isUnit_card I hI h_card`.

end Ideal.Quotient.FixedPoints
