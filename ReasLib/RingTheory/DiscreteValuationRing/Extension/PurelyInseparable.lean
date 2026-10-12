/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Purely inseparable ramification

This leaf owns the uniformizer and association bridges used by the purely inseparable
ramification statement.  Chapter 15 exposes only a tagged recall of the main theorem; the
supporting declarations remain available to localization and normalization consumers.

@stack 09E6
-/

open Ideal IsLocalRing IsExtensionOfDiscreteValuationRings

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

-- Local instance justification (defeq pin): use the canonical fraction-field algebra and tower
-- chosen by the DVR extension API while stating the fraction-field specialization.
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Association of two powers of a DVR uniformizer forces equality of their exponents. -/
@[stacks 09E6 "uniformizer powers have unique exponents"]
lemma uniformizer_power_associated_injective {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (π : R)
    (hπ : maximalIdeal R = Ideal.span ({π} : Set R)) {m n : ℕ}
    (hassoc : Associated (π ^ m) (π ^ n)) : m = n := sorry
-- Proof strategy: convert `hπ` to irreducibility with
-- `IsDiscreteValuationRing.irreducible_iff_uniformizer`, use
-- `IsDiscreteValuationRing.addVal_eq_iff_associated` on `hassoc`, and simplify the additive
-- valuation of the two powers of the uniformizer.

/-- The image of a source uniformizer is associated to the target uniformizer raised to the
extension ramification index. -/
@[stacks 09E6 "uniformizer image and ramification index"]
lemma uniformizer_image_associated_uniformizer_pow_ramificationIndex
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B)) :
    Associated (algebraMap A B πA) (πB ^ ramificationIndex A B) := sorry
-- Proof strategy: obtain the mapped-maximal-ideal equality from
-- `ramificationIndex_eq_iff A B (ramificationIndex A B)`, rewrite both maximal ideals with
-- `hπA` and `hπB`, use `Ideal.map_span` and `Ideal.span_singleton_pow`, and conclude with
-- `Ideal.span_singleton_eq_span_singleton`.

/-- In a positive-characteristic purely inseparable fraction-field extension, the DVR
ramification index is a power of the residue characteristic. -/
@[stacks 09E6 "purely inseparable ramification index"]
theorem ramificationIndex_eq_pow_of_isPurelyInseparable
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing A) p]
    [IsPurelyInseparable (FractionRing A) (FractionRing B)] :
    ∃ n : ℕ, ramificationIndex A B = p ^ n := sorry
-- Proof strategy: choose irreducible uniformizers using
-- `IsDiscreteValuationRing.exists_irreducible`; use `isPurelyInseparable_iff_pow_mem` to put a
-- `p`-power of the target uniformizer in the image of `FractionRing A`; clear its denominator;
-- decompose nonzero DVR elements with `IsDiscreteValuationRing.associated_pow_irreducible`; then
-- combine `uniformizer_image_associated_uniformizer_pow_ramificationIndex` and
-- `uniformizer_power_associated_injective` to show the ramification index divides `p ^ n`, and
-- finish with `Nat.dvd_prime_pow`.
