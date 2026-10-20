/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.ArtinSchreier
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.IntegralClosure
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Residue
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.TotalRamification
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Artin--Schreier ramification over a discrete valuation ring

The source-facing generator is bundled explicitly, while the ramification alternatives use the
field-model owners `DVR.Field.IsUnramified` and `DVR.Field.IsTotallyRamified`.  The residue branch
keeps the normalization DVR as an existential witness, so no noncanonical normalization instance
is registered globally.

@stack 09F0
-/

open Ideal IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped IntermediateField

universe u v w

namespace DVR.ArtinSchreier

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L]
variable [IsScalarTower A K L]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- The explicit root and generator data for an Artin--Schreier extension with parameter `ξ`. -/
@[stacks 09F0 "Artin--Schreier generator data"]
structure Generator (ξ : K) where
  /-- The chosen Artin--Schreier root. -/
  root : L
  /-- The defining equation of the chosen root. -/
  equation : root ^ p - root = algebraMap K L ξ
  /-- The chosen root generates the ambient field over `K`. -/
  generates : IntermediateField.adjoin K ({root} : Set L) = ⊤

namespace Generator

/-- The defining equation and generation condition carried by a generator. -/
@[stacks 09F0 "Artin--Schreier generator specification"]
theorem spec {ξ : K} (h : Generator (K := K) (L := L) (p := p) ξ) :
    h.root ^ p - h.root = algebraMap K L ξ ∧
      IntermediateField.adjoin K ({h.root} : Set L) = ⊤ := sorry
-- Proof strategy: assemble the conjunction from `h.equation` and `h.generates`.

/-- A generated Artin--Schreier root makes the ambient extension finite-dimensional. -/
@[stacks 09F0 "Artin--Schreier generator finite-dimensionality"]
theorem finiteDimensional {ξ : K}
    (h : Generator (K := K) (L := L) (p := p) ξ) :
    FiniteDimensional K L := sorry
-- Proof strategy: the chosen root is integral over `K` because it satisfies the monic polynomial
-- `X ^ p - X - C ξ`; combine finiteness of the simple adjoin with `h.generates` to transport the
-- finite-dimensional instance to `L`.

end Generator

/-- The normalization residue alternative in the Artin--Schreier classification.

The DVR witness is deliberately existential: installing it globally would create a competing
normalization owner for consumers that use a different integral-closure instance. -/
@[stacks 09F0 "Artin--Schreier inseparable residue alternative"]
def ResidueCase (A : Type u) (L : Type w) (p : ℕ)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] : Prop :=
  ∃ hB : IsDiscreteValuationRing (integralClosure A L),
    -- Local instance justification (proof-local temporary data): the source alternative carries
    -- the normalization DVR only for the two residue-field clauses below.
    letI : IsDiscreteValuationRing (integralClosure A L) := hB
    -- Local instance justification (proof-local temporary data): the fraction-field tower supplies
    -- the normalization extension needed to interpret weak unramifiedness.
    letI : IsExtensionOfDiscreteValuationRings A (integralClosure A L) :=
      IsExtensionOfDiscreteValuationRings.ofFractionField
    WeaklyUnramified A (integralClosure A L) ∧
      IsPurelyInseparable (ResidueField A) (ResidueField (integralClosure A L)) ∧
        Module.finrank (ResidueField A) (ResidueField (integralClosure A L)) = p

namespace ResidueCase

/-- The three clauses bundled by `ResidueCase`. -/
@[stacks 09F0 "Artin--Schreier residue alternative specification"]
theorem spec {A : Type u} {L : Type w} {p : ℕ}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L]
    (h : ResidueCase A L p) :
    ∃ hB : IsDiscreteValuationRing (integralClosure A L),
      letI : IsDiscreteValuationRing (integralClosure A L) := hB
      letI : IsExtensionOfDiscreteValuationRings A (integralClosure A L) :=
        IsExtensionOfDiscreteValuationRings.ofFractionField
      WeaklyUnramified A (integralClosure A L) ∧
        IsPurelyInseparable (ResidueField A) (ResidueField (integralClosure A L)) ∧
          Module.finrank (ResidueField A) (ResidueField (integralClosure A L)) = p := sorry
-- Proof strategy: unfold `ResidueCase` and return the supplied existential witness and its three
-- conjuncts unchanged.

end ResidueCase

end

section Canonical

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type w} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable {p : ℕ} [Fact p.Prime] [CharP (FractionRing A) p]

/-- Lemma 15.116.11: the Artin--Schreier generator is Galois and falls into the four source
ramification alternatives over the canonical fraction field. -/
@[stacks 09F0 "Lemma 15.116.11 Artin--Schreier ramification classification"]
theorem classify {ξ : FractionRing A}
    (h : Generator (K := FractionRing A) (L := L) (p := p) ξ) :
    IsGalois (FractionRing A) L ∧
      (Module.finrank (FractionRing A) L = 1 ∨
        (Module.finrank (FractionRing A) L = p ∧
          DVR.Field.IsUnramified A (FractionRing A) L) ∨
        (Module.finrank (FractionRing A) L = p ∧
          DVR.Field.IsTotallyRamified A (FractionRing A) L) ∨
        ResidueCase A L p) := sorry
-- Proof strategy: first prove the generated Artin--Schreier extension Galois and split its degree
-- into `1` or the prime `p`.  In degree `p`, apply the fundamental identity for primes above the
-- maximal ideal.  Prime factorization of `p` leaves: unramified branches, one totally ramified
-- branch, or one weakly-unramified branch whose residue extension has degree `p`; split the latter
-- residue extension into separable versus purely inseparable to obtain exactly the four cases.

/-- Lemma 15.116.11, Galois conclusion: an Artin--Schreier extension generated by the chosen
root is Galois. -/
@[stacks 09F0 "Lemma 15.116.11, Galois conclusion"]
theorem isGalois {ξ : FractionRing A}
    (h : Generator (K := FractionRing A) (L := L) (p := p) ξ) :
    IsGalois (FractionRing A) L := sorry
-- Proof strategy: project the first component of `classify h` (or use the standard
-- Artin--Schreier normality and separability argument directly).

/-- Lemma 15.116.11, cases (1)-(4): an Artin--Schreier extension lies in one of the four
ramification alternatives over the canonical fraction field. -/
@[stacks 09F0 "Lemma 15.116.11, cases (1)-(4), ramification alternatives"]
theorem ramificationAlternatives {ξ : FractionRing A}
    (h : Generator (K := FractionRing A) (L := L) (p := p) ξ) :
    Module.finrank (FractionRing A) L = 1 ∨
      (Module.finrank (FractionRing A) L = p ∧
        DVR.Field.IsUnramified A (FractionRing A) L) ∨
      (Module.finrank (FractionRing A) L = p ∧
        DVR.Field.IsTotallyRamified A (FractionRing A) L) ∨
      ResidueCase A L p := sorry
-- Proof strategy: project the second component of `classify h`.

/-- If the Artin--Schreier parameter comes from the DVR, the trivial or unramified alternative is
forced. -/
@[stacks 09F0 "Lemma 15.116.11 (A), integral-parameter implication"]
theorem of_mem {ξ : FractionRing A}
    (h : Generator (K := FractionRing A) (L := L) (p := p) ξ)
    (hξ : ∃ a : A, algebraMap A (FractionRing A) a = ξ) :
    Module.finrank (FractionRing A) L = 1 ∨
      (Module.finrank (FractionRing A) L = p ∧
        DVR.Field.IsUnramified A (FractionRing A) L) := sorry
-- Proof strategy: write `ξ` as an element of `A`.  The chosen root then satisfies a monic
-- Artin--Schreier polynomial over `A`; its derivative is `-1`, so the monogenic algebra is etale.
-- Identify that algebra with the normalization and obtain unramified branches.  Apply
-- `ramificationAlternatives h`; the totally ramified and inseparable-residue cases collapse to
-- degree one, leaving precisely the displayed alternatives.

/-- A pole of positive order prime to `p` forces the totally ramified degree-`p` alternative.
The branch ramification index is therefore `p` by
`DVR.Field.IsTotallyRamified.ramificationIdx_eq_finrank`. -/
@[stacks 09F0 "Lemma 15.116.11 (B), prime-to-p denominator"]
theorem totallyRamified {ξ : FractionRing A}
    (h : Generator (K := FractionRing A) (L := L) (p := p) ξ)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hndiv : ¬ p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A (FractionRing A) (a : A) /
      (algebraMap A (FractionRing A) π) ^ n) :
    Module.finrank (FractionRing A) L = p ∧
      DVR.Field.IsTotallyRamified A (FractionRing A) L := sorry
-- Proof strategy: inspect `ramificationAlternatives h`.  Transport the equation to each DVR
-- branch and normalize the pole as a unit divided by a uniformizer to exponent `n * e`.  For every
-- non-totally-ramified alternative, `e = 1` and the Artin--Schreier pole calculation forces
-- `p ∣ n`, contradicting `hndiv`; degree one is excluded by the same valuation equation.

/-- A pole of order divisible by `p` with non-`p`th-power residue gives the weakly unramified
purely inseparable residue alternative. -/
@[stacks 09F0 "Lemma 15.116.11 (C), divisible-p residue alternative"]
theorem residueCase {ξ : FractionRing A}
    (h : Generator (K := FractionRing A) (L := L) (p := p) ξ)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (ha : ¬ ∃ b : ResidueField A, b ^ p = residue A (a : A))
    (hξ : ξ = algebraMap A (FractionRing A) (a : A) /
      (algebraMap A (FractionRing A) π) ^ n) :
    ResidueCase A L p := sorry
-- Proof strategy: apply `ramificationAlternatives h`.  Scale a root by `π ^ (n / p)` and reduce
-- its equation in each of the degree-one, unramified, and totally ramified branches; separability
-- and the branch residue maps would make `residue A a` a `p`th power, contradicting `ha`.
-- Therefore only the weakly-unramified purely inseparable residue branch remains.

end Canonical

end DVR.ArtinSchreier

end
