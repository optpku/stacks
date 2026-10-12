/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Kummer.Generator
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.TotalRamification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
public import Mathlib.Algebra.CharP.MixedCharZero
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ramification of Kummer--Artin--Schreier presentations

This file owns the ramification classification of a Kummer--Artin--Schreier root presentation over
a mixed-characteristic DVR.  The fraction field and normalization are kept canonical, while the
residue-field alternative is bundled behind one reusable predicate.

@stack 09F3
-/

open Ideal IsLocalRing
open IsExtensionOfDiscreteValuationRings
open DVR.Field

universe u v

namespace KummerArtinSchreier.Ramification

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [Fact p.Prime] [MixedCharZero A p]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]

/-- The inseparable residue alternative for a normalization branch: the normalization is a DVR,
the extension is weakly unramified, and its residue extension is purely inseparable of degree
`p`.  The existential DVR witness is centralized here because all three clauses use it. -/
@[stacks 09F3 "inseparable residue ramification alternative"]
def HasInseparableResidue (A : Type u) (L : Type v) (p : ℕ)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] : Prop :=
  ∃ hB : IsDiscreteValuationRing (integralClosure A L),
    -- Local instance justification (proof-local temporary data): the source alternative asserts
    -- the DVR structure as part of its existential branch data.
    letI : IsDiscreteValuationRing (integralClosure A L) := hB
    -- Local instance justification (proof-local temporary data): the DVR witness activates the
    -- canonical normalization extension supplied by the fraction-field tower.
    letI : IsExtensionOfDiscreteValuationRings A (integralClosure A L) :=
      IsExtensionOfDiscreteValuationRings.ofFractionField
    WeaklyUnramified A (integralClosure A L) ∧
      IsPurelyInseparable (ResidueField A) (ResidueField (integralClosure A L)) ∧
      Module.finrank (ResidueField A) (ResidueField (integralClosure A L)) = p

/-- The bundled inseparable-residue alternative is equivalent to its DVR, weakly-unramified,
purely-inseparable, and residue-degree clauses. -/
@[stacks 09F3 "inseparable residue alternative characterization"]
theorem hasInseparableResidue_iff :
    HasInseparableResidue A L p ↔
      ∃ hB : IsDiscreteValuationRing (integralClosure A L),
        -- Local instance justification (proof-local temporary data): expose the DVR witness carried
        -- by the source alternative only while stating its three branch clauses.
        letI : IsDiscreteValuationRing (integralClosure A L) := hB
        -- Local instance justification (proof-local temporary data): the exposed DVR witness
        -- activates the canonical normalization extension supplied by the fraction-field tower.
        letI : IsExtensionOfDiscreteValuationRings A (integralClosure A L) :=
          IsExtensionOfDiscreteValuationRings.ofFractionField
        WeaklyUnramified A (integralClosure A L) ∧
          IsPurelyInseparable (ResidueField A) (ResidueField (integralClosure A L)) ∧
          Module.finrank (ResidueField A) (ResidueField (integralClosure A L)) = p := sorry
-- Proof strategy: unfold `HasInseparableResidue`; both sides use the same existential DVR witness
-- and the same proof-local normalization-extension instance.

/-- A mixed-characteristic Kummer--Artin--Schreier root presentation defines a Galois extension of
the fraction field. -/
@[stacks 09F3 "Lemma 15.116.14, Galois conclusion"]
theorem isGalois
    (h : RootPresentation A (FractionRing A) L p) :
    IsGalois (FractionRing A) L := sorry
-- Proof strategy: use `h.finiteDimensional`.  Affinely translate the generator to
-- `y = 1 + (1 - h.ζ) * h.z`; the quotient identity gives a radical equation `y ^ p = η`, and
-- primitivity of `h.ζ` gives the full Kummer factorization of `X ^ p - C η` in `L`.  The translated
-- generator still generates `L`, so its mapped minimal polynomial splits and the extension is
-- normal.  Mixed characteristic gives characteristic zero and hence separability; conclude with
-- `isGalois_iff`.

/-- A Kummer--Artin--Schreier root presentation is trivial, unramified of degree `p`, totally
ramified of degree `p`, or has the bundled inseparable residue alternative. -/
@[stacks 09F3 "Lemma 15.116.14, cases (1)-(4): ramification classification"]
theorem classification
    (h : RootPresentation A (FractionRing A) L p) :
    Module.finrank (FractionRing A) L = 1 ∨
      (Module.finrank (FractionRing A) L = p ∧
        DVR.Field.IsUnramified A (FractionRing A) L) ∨
      (Module.finrank (FractionRing A) L = p ∧
        IsTotallyRamified A (FractionRing A) L) ∨
      HasInseparableResidue A L p := sorry
-- Proof strategy: install the finite-dimensional and Galois facts supplied by the root
-- presentation.  The radical presentation bounds the degree by the prime `p`, so it is `1` or
-- `p`.  In the degree-`p` case, apply the DVR fundamental ramification identity to the
-- normalization.  Split according to ramification index and separability of the residue extension:
-- `e = 1` with separable residue is unramified, `e = p` is totally ramified, and the remaining
-- `e = 1`, residue-degree-`p` branch supplies the DVR witness, weak unramifiedness, and purely
-- inseparable residue extension required by `HasInseparableResidue`.

/-- If the right-hand side of the root equation comes from the DVR, the extension is trivial or
unramified of degree `p`. -/
@[stacks 09F3 "Lemma 15.116.14 (A): integral right-hand side"]
theorem trivialOrUnramified
    (h : RootPresentation A (FractionRing A) L p)
    (h_integral : ∃ a : A, algebraMap A (FractionRing A) a = h.ξ) :
    Module.finrank (FractionRing A) L = 1 ∨
      (Module.finrank (FractionRing A) L = p ∧
        DVR.Field.IsUnramified A (FractionRing A) L) := sorry
-- Proof strategy: use the integral witness for `h.ξ` in the translated Kummer equation.  The
-- resulting monogenic normalization is finite etale over `A`, hence the field extension is
-- unramified.  Combine the prime-degree bound from the root presentation with the trivial case to
-- obtain precisely the displayed disjunction.

/-- A positive denominator exponent prime to `p`, with unit numerator, gives a totally ramified
extension of degree `p`. -/
@[stacks 09F3 "Lemma 15.116.14 (B): nondivisible denominator exponent"]
theorem totallyRamified
    (h : RootPresentation A (FractionRing A) L p)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (h_not_dvd : ¬ p ∣ n) (a : Aˣ)
    (hξ : h.ξ = algebraMap A (FractionRing A) (a : A) /
      algebraMap A (FractionRing A) π ^ n) :
    Module.finrank (FractionRing A) L = p ∧
      IsTotallyRamified A (FractionRing A) L := sorry
-- Proof strategy: evaluate the translated radical equation with the valuation normalized by `π`.
-- The unit numerator and `p ∤ n` force the ramification index to be divisible by `p`.  The
-- root-presentation degree is at most the prime `p`, so the degree and ramification index are both
-- `p`; apply the field-level total-ramification criterion using `hπ`.

/-- A positive denominator exponent divisible by `p`, whose unit numerator is not a residue
`p`th power, gives the bundled inseparable residue alternative. -/
@[stacks 09F3 "Lemma 15.116.14 (C): divisible denominator exponent"]
theorem inseparableResidue
    (h : RootPresentation A (FractionRing A) L p)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (h_dvd : p ∣ n) (a : Aˣ)
    (ha : ¬ ∃ b : ResidueField A, b ^ p = residue A (a : A))
    (hξ : h.ξ = algebraMap A (FractionRing A) (a : A) /
      algebraMap A (FractionRing A) π ^ n) :
    HasInseparableResidue A L p := sorry
-- Proof strategy: write `n = p * m`, scale the translated generator by `π ^ m`, and obtain an
-- integral equation whose reduction is `X ^ p - residue A a`.  Normalize the resulting integral
-- algebra.  The residue nonpower hypothesis makes this reduction irreducible and purely
-- inseparable of degree `p`, while the scaled equation keeps ramification index one.  Package the
-- normalization DVR witness, the maximal-ideal equality giving `WeaklyUnramified`, and the residue
-- finrank computation into `HasInseparableResidue`.

end KummerArtinSchreier.Ramification
