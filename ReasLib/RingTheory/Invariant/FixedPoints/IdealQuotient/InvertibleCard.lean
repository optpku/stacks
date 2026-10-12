/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.FixedPoints.IdealQuotient
public import ReasLib.RingTheory.Invariant.Quotient.InvertibleCard

@[expose] public section

/-!
# Extended fixed-point ideals when the group order is invertible

For an ideal of a fixed-point subring, Reynolds exactness identifies its contraction after
extension and shows that the canonical map to the fixed points of the ambient quotient is
bijective.

@stack 0H36
-/

universe u v

namespace FixedPoints.Quotient

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R]
variable [Finite G]

/-- Extending an ideal of the fixed-point subring and contracting it back recovers the original
ideal when the order of the acting group is a unit. -/
@[stacks 0H36 "extension-contraction for fixed-point ideals"]
theorem comap_ideal_eq_of_isUnit_card (J : Ideal (FixedPoints.subring R G))
    (h_card : IsUnit (Nat.card G : R)) :
    Ideal.comap (FixedPoints.subring R G).subtype (ideal J) = J := sorry
-- Proof strategy: `Ideal.le_comap_map` gives one inclusion.  For the reverse inclusion, send a
-- fixed element of `ideal J` to its class in `FixedPoints.subring R G ⧸ J`; `map_mk` puts this
-- class in the kernel of `map J`.  Apply `kernel_pow J`, compare the coefficient of
-- `Nat.card G - 1` in `(X - C a) ^ Nat.card G = X ^ Nat.card G`, and cancel the image of
-- `Nat.card G`, which is a unit by `FixedPoints.isUnit_iff` and `IsUnit.map`.  The resulting zero
-- class is exactly membership in `J` by `Ideal.Quotient.eq_zero_iff_mem`.

/-- The canonical map from a fixed-subring quotient is injective when the group order is a unit. -/
@[stacks 0H36 "injectivity for an extended fixed-point ideal quotient"]
theorem map_injective_of_isUnit_card (J : Ideal (FixedPoints.subring R G))
    (h_card : IsUnit (Nat.card G : R)) :
    Function.Injective (map J) := sorry
-- Proof strategy: rewrite the source ideal using `comap_ideal_eq_of_isUnit_card J h_card`, then
-- identify `map J` with `Ideal.Quotient.fixedPointsMap (ideal J) (ideal_isStable J)` through
-- `mapOfLE`; conclude with `Ideal.Quotient.FixedPoints.map_injective`.

/-- The canonical map from a fixed-subring quotient is surjective when the group order is a unit. -/
@[stacks 0H36 "surjectivity for an extended fixed-point ideal quotient"]
theorem map_surjective_of_isUnit_card (J : Ideal (FixedPoints.subring R G))
    (h_card : IsUnit (Nat.card G : R)) :
    Function.Surjective (map J) := sorry
-- Proof strategy: after the same source-ideal rewrite from
-- `comap_ideal_eq_of_isUnit_card J h_card`, identify `map J` with the generic stable-quotient map
-- and apply `Ideal.Quotient.FixedPoints.map_surjective_of_isUnit_card` to `ideal_isStable J`.

/-- The canonical map from a fixed-subring quotient is bijective when the group order is a unit. -/
@[stacks 0H36 "bijectivity for an extended fixed-point ideal quotient"]
theorem map_bijective_of_isUnit_card (J : Ideal (FixedPoints.subring R G))
    (h_card : IsUnit (Nat.card G : R)) :
    Function.Bijective (map J) := sorry
-- Proof strategy: combine `map_injective_of_isUnit_card J h_card` and
-- `map_surjective_of_isUnit_card J h_card`.

end FixedPoints.Quotient
