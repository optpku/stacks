module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.RingTheory.Ideal.OneAdd
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Power maps on `1 + I`

This leaf owns the locally nilpotent power-map and quotient-root criteria on
the canonical multiplicative submonoid `Ideal.oneAdd I`.

@stack 0CAP
-/

universe u

namespace Ideal.IsLocallyNilpotent

variable {R : Type u} [CommRing R]

/-- Lemma 10.32.8 (1): the nth-power map on `1 + I` is bijective when `I` is
locally nilpotent and `n` is invertible modulo `I`. -/
@[stacks 0CAP "(1), power bijection on oneAdd"]
theorem oneAdd_pow_bijective {I : Ideal R} (hI : I.IsLocallyNilpotent)
    {n : ℕ} (hn : 1 ≤ n) (hn_unit : IsUnit (n : R ⧸ I)) :
    Function.Bijective (fun x : I.oneAdd ↦ x ^ n) := sorry

/-- The power bijection on `1 + I` gives a unique nth root for every element
of that submonoid. -/
@[stacks 0CAP "unique root on oneAdd"]
theorem oneAdd_existsUnique_pow_eq {I : Ideal R} (hI : I.IsLocallyNilpotent)
    {n : ℕ} (hn : 1 ≤ n) (hn_unit : IsUnit (n : R ⧸ I)) (u : I.oneAdd) :
    ∃! v : I.oneAdd, v ^ n = u := sorry

/-- Lemma 10.32.8 (2): an nth root of a unit lifts across a locally
nilpotent quotient exactly when its quotient root exists. -/
@[stacks 0CAP "(2), unit-valued quotient root criterion"]
theorem units_exists_pow_iff_quotient {I : Ideal R} (hI : I.IsLocallyNilpotent)
    {n : ℕ} (hn : 1 ≤ n) (hn_unit : IsUnit (n : R ⧸ I)) (a : Rˣ) :
    (∃ b : Rˣ, b ^ n = a) ↔
      ∃ bbar : (R ⧸ I)ˣ,
        bbar ^ n = Units.map (Ideal.Quotient.mk I).toMonoidHom a := sorry

/-- Ring-element form of the unit-valued quotient root criterion. -/
@[stacks 0CAP "(2), ring-element quotient root criterion"]
theorem isUnit_exists_pow_iff_quotient {I : Ideal R} (hI : I.IsLocallyNilpotent)
    {n : ℕ} (hn : 1 ≤ n) (hn_unit : IsUnit (n : R ⧸ I))
    {a : R} (ha : IsUnit a) :
    (∃ b : R, b ^ n = a) ↔
      ∃ bbar : R ⧸ I, bbar ^ n = Ideal.Quotient.mk I a := sorry

end Ideal.IsLocallyNilpotent
