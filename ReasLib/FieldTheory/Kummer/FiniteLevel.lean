/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RootsOfUnity.KummerArtinSchreier
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.CharP.MixedCharZero
public import Mathlib.Tactic.CrossRefAttribute
import ReasLib.FieldTheory.Kummer.Generator

/-!
@stack 09F4
@stack 09F5
-/

@[expose] public section

open Polynomial

namespace KummerArtinSchreier

universe u v w u' v' w'

namespace RootEquation

/-- A Kummer--Artin--Schreier root equation has finite level over a local coefficient ring
when `(1 - ζ) ^ p * ξ` is the image of an element of its maximal ideal.  This is the
uniformizer-free source definition; denominator coordinates are introduced separately in
`FiniteLevel.Equation`. -/
@[stacks 09F4 "source finite-level condition"]
def IsFiniteLevel
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : RootEquation B L M p) : Prop :=
  ∃ a : B,
    a ∈ IsLocalRing.maximalIdeal B ∧
      algebraMap B L a = algebraMap B L (1 - h.ζ) ^ p * h.ξ

namespace IsFiniteLevel

/-- The source finite-level predicate exposes its maximal-ideal witness without unfolding the
definition at downstream call sites. -/
@[stacks 09F4 "finite-level source condition specification"]
theorem spec
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    {h : RootEquation B L M p} (hh : h.IsFiniteLevel) :
    ∃ a : B,
      a ∈ IsLocalRing.maximalIdeal B ∧
        algebraMap B L a = algebraMap B L (1 - h.ζ) ^ p * h.ξ := sorry
-- Proof strategy: unfold `RootEquation.IsFiniteLevel`; this is its defining existential.

end IsFiniteLevel

end RootEquation

namespace RootPresentation

/-- A generating root presentation has finite level when its underlying root equation does. -/
@[stacks 09F4 "finite-level condition on a generating root presentation"]
abbrev IsFiniteLevel
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : RootPresentation B L M p) : Prop :=
  h.toRootEquation.IsFiniteLevel

namespace IsFiniteLevel

/-- The generating presentation inherits the source witness specification from its root equation. -/
@[stacks 09F4 "root presentation finite-level specification"]
theorem spec
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    {h : RootPresentation B L M p} (hh : h.IsFiniteLevel) :
    ∃ a : B,
      a ∈ IsLocalRing.maximalIdeal B ∧
        algebraMap B L a = algebraMap B L (1 - h.ζ) ^ p * h.ξ := sorry
-- Proof strategy: unfold the `RootPresentation.IsFiniteLevel` abbreviation and apply the root
-- equation specification.

end IsFiniteLevel

end RootPresentation

namespace FiniteLevel

/-!
# Finite-level Kummer--Artin--Schreier extensions

The source condition is the uniformizer-free predicate `RootEquation.IsFiniteLevel`, inherited by
`RootPresentation.IsFiniteLevel`.
An `Equation` adds one denominator coordinate system, while a `Presentation` records a coordinate
system whose rational ratio is minimal for a fixed primitive root and polynomial.  Thus the root-theoretic definition, the
valuation computation, and the exact level invariant remain separate reusable layers.

@stack 09F4
@stack 09F5
-/

/-- The source setting for finite level: a mixed-characteristic `(0, p)` DVR and its fraction
field.  This proof-only support does not install noncanonical global instances. -/
structure IsSource
    (B : Type u) [CommRing B]
    (L : Type v) [Field L] [Algebra B L]
    (p : ℕ) [Fact p.Prime] : Prop where
  domain : IsDomain B
  dvr : @IsDiscreteValuationRing B _ domain
  fractionRing : IsFractionRing B L
  mixedCharacteristic : MixedCharZero B p

/-- One generating Kummer--Artin--Schreier equation with explicit, possibly unnormalized,
denominator data.  This reusable data layer does not assert the source DVR setting. -/
@[stacks 09F4 "Kummer--Artin--Schreier finite-level equation"]
structure Equation
    (B : Type u) [CommRing B]
    (L : Type v) [Field L] [Algebra B L]
    (M : Type w) [Field M] [Algebra L M]
    (p : ℕ) extends RootPresentation B L M p where
  /-- A denominator parameter in the coefficient ring. -/
  π : B
  /-- The exponent relating `1 - ζ` to the denominator parameter. -/
  e : ℕ
  /-- The denominator exponent of the right-hand side. -/
  n : ℕ
  /-- The root-of-unity exponent is positive. -/
  e_pos : 0 < e
  /-- The element `1 - ζ` is associated to `π ^ e`. -/
  associated : Associated (1 - ζ) (π ^ e)
  /-- The numerator of the right-hand side. -/
  a : B
  /-- The right-hand side is represented by the chosen denominator. -/
  denominator : ξ = algebraMap B L a / (algebraMap B L π) ^ n

/-- The underlying generating root presentation of a denominator equation. -/
@[stacks 09F4 "root presentation underlying a finite-level equation"]
abbrev Equation.root
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) : RootPresentation B L M p := h.toRootPresentation

/-- The rational denominator ratio attached to one equation. -/
@[stacks 09F5 "rational level of a finite-level equation"]
def Equation.level
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) : ℚ := (h.n : ℚ) / h.e

/-- A denominator equation is normalized when its numerator has no further uniformizer factor.  At
denominator exponent zero no unit condition is needed; the separate finite-level predicate owns
the assertion that `π` is a uniformizer. -/
@[stacks 09F5 "normalized finite-level denominator equation"]
def Equation.IsNormalized
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) : Prop :=
  h.n = 0 ∨ IsUnit h.a

/-- A uniformizer coordinate equation satisfies finite level exactly when its underlying root
equation satisfies the source maximal-ideal condition.  No normalization of the numerator is
imposed here. -/
@[stacks 09F4 "source finite-level condition in denominator coordinates"]
def Equation.IsFiniteLevel
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
  (h : Equation B L M p) : Prop :=
  Irreducible h.π ∧ h.root.IsFiniteLevel

/-- The displayed polynomial is the canonical quotient polynomial attached to `ζ`. -/
@[stacks 09F4 "canonical polynomial condition on a denominator equation"]
def Equation.IsCanonical
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) : Prop :=
  h.P = KummerArtinSchreier.polynomial p h.ζ

/-- A source finite-level presentation over a mixed-characteristic DVR.  Its rational ratio is
minimal among all uniformizer coordinate equations with the same primitive root and polynomial,
as in the source definition of level. -/
@[stacks 09F4 "Kummer--Artin--Schreier finite-level presentation"]
structure Presentation
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (L : Type v) [Field L] [Algebra B L] [IsFractionRing B L]
    (M : Type w) [Field M] [Algebra L M]
    (p : ℕ) [Fact p.Prime] extends Equation B L M p where
  /-- The source ring has mixed characteristic `(0, p)`. -/
  mixedCharacteristic : MixedCharZero B p
  /-- The chosen uniformizer equation satisfies the source finite-level condition. -/
  finiteLevel : toEquation.IsFiniteLevel
  /-- The displayed polynomial is the canonical quotient polynomial. -/
  canonical : toEquation.IsCanonical
  /-- The displayed root generates a degree-`p` extension. -/
  degreeP : Module.finrank L M = p
  /-- Only the generating root and denominator coordinates vary; `ζ` and `P` remain fixed.
  Candidates need not be normalized or separately satisfy finite level. -/
  minimal :
    ∀ Q : Equation B L M p,
      Q.ζ = ζ → Q.P = P → Irreducible Q.π → toEquation.level ≤ Q.level

/-- The level of a minimal finite-level presentation. -/
@[stacks 09F5 "level of a finite-level presentation"]
abbrev Presentation.level
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : ℚ := h.toEquation.level

/-- In the source DVR/fraction-field setting, a degree-`p` extension is of finite level when it
has a generating canonical root equation for which `(1 - ζ) ^ p * ξ` comes from the maximal
ideal.  The proof-only setting is part of the predicate, preserving the local-ring API. -/
@[stacks 09F4 "Kummer--Artin--Schreier finite-level extension"]
def IsExtension
    (B : Type u) [CommRing B] [IsLocalRing B]
    (L : Type v) [Field L] [Algebra B L]
    (M : Type w) [Field M] [Algebra L M]
    (p : ℕ) [Fact p.Prime] : Prop :=
  IsSource B L p ∧ ∃ h : RootPresentation B L M p,
    h.P = KummerArtinSchreier.polynomial p h.ζ ∧
      h.IsFiniteLevel ∧ Module.finrank L M = p

/-- A finite-level extension has exact level `l` when a finite-level presentation realizes the
minimal ratio `l`. -/
@[stacks 09F5 "Kummer--Artin--Schreier extension at a finite level"]
def IsAtLevel
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (L : Type v) [Field L] [Algebra B L] [IsFractionRing B L]
    (M : Type w) [Field M] [Algebra L M]
    (p : ℕ) (l : ℚ) [Fact p.Prime] : Prop :=
  ∃ h : Presentation B L M p, l = h.level

namespace Equation

namespace IsNormalized

/-- A normalized equation with positive denominator exponent has unit numerator. -/
@[stacks 09F5 "unit numerator of a normalized finite-level equation"]
theorem isUnit
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    {h : Equation B L M p} (hh : h.IsNormalized) (hn : 0 < h.n) : IsUnit h.a := sorry
-- Proof strategy: unfold `Equation.IsNormalized`; eliminate the `h.n = 0` branch using `hn` and
-- return the remaining unit assertion.

end IsNormalized

/-- The denominator field of an equation exposes the source equality for `ξ`. -/
@[stacks 09F4 "finite-level denominator equation"]
theorem denominator_eq
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) :
    h.ξ = algebraMap B L h.a / (algebraMap B L h.π) ^ h.n := sorry
-- Proof strategy: return the structure field `h.denominator`.

/-- The root equation can be read directly in terms of its numerator and denominator. -/
@[stacks 09F4 "evaluation of a finite-level denominator equation"]
theorem eval_eq_denominator
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) :
    aeval h.z (h.P.map (algebraMap B L)) =
      algebraMap L M (algebraMap B L h.a / (algebraMap B L h.π) ^ h.n) := sorry
-- Proof strategy: rewrite the stored root equation `h.eval_eq` by `h.denominator_eq`.

/-- The canonical polynomial satisfies the displayed denominator equation. -/
@[stacks 09F4 "canonical finite-level denominator equation"]
theorem canonical_eval_eq_denominator
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) (hc : h.IsCanonical) :
    aeval h.z ((KummerArtinSchreier.polynomial p h.ζ).map (algebraMap B L)) =
      algebraMap L M (algebraMap B L h.a / (algebraMap B L h.π) ^ h.n) := sorry
-- Proof strategy: unfold `Equation.IsCanonical`, rewrite the polynomial with `hc`, and apply
-- `h.eval_eq_denominator`.

/-- The finite-level condition exposes that `π` is a uniformizer. -/
@[stacks 09F4 "uniformizer in a finite-level equation"]
theorem irreducible
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) (hh : h.IsFiniteLevel) : Irreducible h.π := hh.1

/-- Only normalized finite-level coordinates satisfy the numerator-independent strict bound. -/
@[stacks 09F4 "strict finite-level denominator bound"]
theorem n_lt
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) (hh : h.IsFiniteLevel) (hnorm : h.IsNormalized) (hp : 0 < p) :
    h.n < p * h.e := sorry
-- Proof strategy: for `n = 0`, use positivity of `p` and `e`.  Otherwise the numerator is a
-- unit, so the source witness has valuation `p * e - n > 0` in the fraction field.

/-- The strict denominator bound is sufficient even for unnormalized coordinates. -/
theorem isFiniteLevel_of_n_lt
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) (hπ : Irreducible h.π) (hn : h.n < p * h.e) :
    h.IsFiniteLevel := sorry
-- Proof strategy: cancellation in the fraction field leaves a positive power of the uniformizer
-- multiplying the numerator and a unit; this gives an explicit maximal-ideal witness.

/-- In normalized uniformizer coordinates, the source condition is equivalent to the strict bound. -/
theorem isFiniteLevel_iff_n_lt
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) (hπ : Irreducible h.π) (hnorm : h.IsNormalized) (hp : 0 < p) :
    h.IsFiniteLevel ↔ h.n < p * h.e :=
  ⟨fun hh => h.n_lt hh hnorm hp, h.isFiniteLevel_of_n_lt hπ⟩

/-- A finite-level denominator equation satisfies the uniformizer-free source condition. -/
@[stacks 09F4 "denominator equation to source finite-level condition"]
theorem root_isFiniteLevel
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) (hh : h.IsFiniteLevel) : h.root.IsFiniteLevel := hh.2

/-- A finite-level denominator equation gives the source finite-level extension property. -/
@[stacks 09F4 "denominator equation to finite-level extension"]
theorem isExtension
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime] [MixedCharZero B p]
    (h : Equation B L M p) (hc : h.IsCanonical) (hh : h.IsFiniteLevel)
    (hdeg : Module.finrank L M = p) :
    IsExtension B L M p :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, h.root, hc, hh.2, hdeg⟩

/-- Changing the primitive root transports canonical coordinates without changing the uniformizer
or either exponent.  This is separate from the fixed-polynomial minimum. -/
theorem exists_changeRoot
    {B : Type u} [CommRing B] [IsDomain B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Equation B L M p) (hc : h.IsCanonical)
    (ζ : B) (hζ : IsPrimitiveRoot ζ p) :
    ∃ Q : Equation B L M p,
      Q.ζ = ζ ∧ Q.IsCanonical ∧ Q.π = h.π ∧ Q.e = h.e ∧ Q.n = h.n := sorry
-- Proof strategy: primitive roots of prime order in a domain are powers of one another, so
-- `1 - ζ = u * (1 - h.ζ)` for a unit `u` of `B`.  Replace `z` by `u⁻¹ * z`, `ξ` and the
-- numerator by `u⁻ᵖ` times their old values.  The quotient identity identifies the new canonical
-- equation.  Scaling by a nonzero base-field scalar preserves the generated extension.

/-- The displayed polynomial of an equation is a quotient polynomial. -/
@[stacks 09F4 "finite-level equation quotient polynomial"]
theorem quotient
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) :
    KummerArtinSchreier.IsQuotient p h.ζ h.P := sorry
-- Proof strategy: return the quotient field of the underlying root equation.

/-- The canonical polynomial attached to an equation is a quotient polynomial. -/
@[stacks 09F4 "canonical finite-level equation quotient polynomial"]
theorem canonical_quotient
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Equation B L M p) (hc : h.IsCanonical) :
    KummerArtinSchreier.IsQuotient p h.ζ (KummerArtinSchreier.polynomial p h.ζ) := sorry
-- Proof strategy: rewrite the target by the canonical equality `hc` and apply `h.quotient`.

/-- A generating denominator equation makes the extension finite-dimensional. -/
@[stacks 09F4 "finite-dimensionality from a finite-level equation"]
theorem finiteDimensional
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Equation B L M p) : FiniteDimensional L M := sorry
-- Proof strategy: apply `RootPresentation.finiteDimensional` to `h.root`; primality is required to
-- make the normalized degree-`p` root equation algebraic.

end Equation

namespace Presentation

/-- A finite-level presentation exposes the source maximal-ideal condition in uniformizer coordinates. -/
@[stacks 09F4 "finite-level condition of a presentation"]
theorem isFiniteLevel
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : h.toEquation.IsFiniteLevel := h.finiteLevel

/-- Minimality forces a positive denominator presentation to have unit numerator. -/
@[stacks 09F5 "normalization of a minimal finite-level presentation"]
theorem isNormalized
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : h.toEquation.IsNormalized := sorry
-- Proof strategy: if `h.n = 0`, use the first normalization branch.  Otherwise, assume the
-- numerator is not a unit.  In the DVR factor it by the uniformizer `h.π`, decrease the denominator
-- exponent accordingly, and build another canonical finite-level equation with strictly smaller
-- rational level and the same `ζ` and `P`, contradicting `h.minimal`.

/-- A presentation canonically gives the corresponding finite-level extension property. -/
@[stacks 09F4 "presentation to finite-level extension"]
theorem isExtension
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : IsExtension B L M p :=
  ⟨⟨inferInstance, inferInstance, inferInstance, h.mixedCharacteristic⟩,
    h.toRootPresentation, h.canonical, h.finiteLevel.2, h.degreeP⟩

/-- A presentation realizes its own exact level. -/
@[stacks 09F5 "presentation at its rational level"]
theorem isAtLevel
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : IsAtLevel B L M p h.level := ⟨h, rfl⟩

/-- A presentation exposes the quotient-polynomial property of its displayed polynomial. -/
@[stacks 09F4 "finite-level presentation quotient polynomial"]
theorem quotient
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) :
    KummerArtinSchreier.IsQuotient p h.ζ h.P := sorry
-- Proof strategy: apply `Equation.quotient h.toEquation`.

/-- The canonical polynomial attached to a presentation is a quotient polynomial. -/
@[stacks 09F4 "canonical finite-level presentation quotient polynomial"]
theorem canonical_quotient
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) :
    KummerArtinSchreier.IsQuotient p h.ζ (KummerArtinSchreier.polynomial p h.ζ) := sorry
-- Proof strategy: apply `Equation.canonical_quotient h.toEquation h.canonical`.

/-- A presentation is minimal among uniformizer equations with the same primitive root and polynomial. -/
@[stacks 09F5 "minimality of a finite-level presentation"]
theorem level_le
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) (Q : Equation B L M p)
    (hζ : Q.ζ = h.ζ) (hP : Q.P = h.P) (hπ : Irreducible Q.π) : h.level ≤ Q.level :=
  h.minimal Q hζ hP hπ

/-- Any two minimal presentations have the same level.  Independence of the primitive root uses
the separate coordinate-transport theorem, rather than enlarging the minimum's candidate set. -/
@[stacks 09F5 "uniqueness of the finite level"]
theorem level_eq
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (P Q : Presentation B L M p) : P.level = Q.level := by
  have compare (P Q : Presentation B L M p) : P.level ≤ Q.level := by
    obtain ⟨R, hζ, hc, hπ, he, hn⟩ :=
      Q.toEquation.exists_changeRoot Q.canonical P.ζ P.isPrimitiveRoot
    have hRP : R.P = P.P := by
      calc
        R.P = KummerArtinSchreier.polynomial p R.ζ := hc
        _ = KummerArtinSchreier.polynomial p P.ζ := congrArg _ hζ
        _ = P.P := P.canonical.symm
    have hRπ : Irreducible R.π := hπ.symm ▸ Q.finiteLevel.1
    have hle := P.level_le R hζ hRP hRπ
    simpa only [Presentation.level, Equation.level, he, hn] using hle
  exact le_antisymm (compare P Q) (compare Q P)

/-- The level of a presentation is nonnegative. -/
@[stacks 09F5 "nonnegativity of a finite level"]
theorem level_nonneg
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : 0 ≤ h.level := sorry
-- Proof strategy: unfold `Presentation.level` and `Equation.level`; the numerator `h.n` is
-- nonnegative and the denominator `h.e` is positive by `h.e_pos`, so rational division is
-- nonnegative.

/-- A finite level lies strictly below the prime degree. -/
@[stacks 09F5 "upper bound for a finite level"]
theorem level_lt
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : h.level < p := sorry
-- Proof strategy: rewrite the rational inequality as `h.n < p * h.e` using positivity of `h.e`,
-- then apply the normalized bound `h.toEquation.n_lt`, using positivity of the prime, and cast
-- the resulting inequality to `ℚ`.

/-- A degree-`p` presentation supplies finite-dimensionality without requiring it as ambient input. -/
@[stacks 09F4 "finite-dimensionality from a finite-level presentation"]
theorem finiteDimensional
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : FiniteDimensional L M := sorry
-- Proof strategy: apply `Equation.finiteDimensional h.toEquation`.

end Presentation

namespace IsExtension

/-- A finite-level extension carries the source DVR, fraction-field, and mixed-characteristic setting. -/
theorem source
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) : IsSource B L p := h.1

/-- The generating root presentation chosen from a source finite-level extension. -/
@[stacks 09F4 "chosen root of a finite-level extension"]
noncomputable def root
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) : RootPresentation B L M p :=
  Classical.choose h.2

/-- The chosen root uses the canonical polynomial attached to its primitive root. -/
@[stacks 09F4 "canonical polynomial of the chosen finite-level root"]
theorem root_canonical
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) :
    h.root.P = KummerArtinSchreier.polynomial p h.root.ζ := (Classical.choose_spec h.2).1

/-- The chosen root satisfies the uniformizer-free source finite-level condition. -/
@[stacks 09F4 "source condition of the chosen finite-level root"]
theorem root_isFiniteLevel
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) : h.root.IsFiniteLevel := (Classical.choose_spec h.2).2.1

/-- The source finite-level owner exposes its complete canonical root specification. -/
@[stacks 09F4 "finite-level root specification"]
theorem exists_root
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) :
    ∃ Q : RootPresentation B L M p,
      Q.P = KummerArtinSchreier.polynomial p Q.ζ ∧
        Q.IsFiniteLevel ∧ Module.finrank L M = p := h.2

/-- A source finite-level extension admits a finite-level denominator coordinate equation. -/
@[stacks 09F4 "finite-level equation specification"]
theorem exists_equation
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) :
    ∃ Q : Equation B L M p, Q.IsCanonical ∧ Q.IsFiniteLevel := sorry
-- Proof strategy: take the maximal-ideal witness from `h.root_isFiniteLevel.spec`.  In the DVR,
-- choose an irreducible uniformizer `π`, express both `1 - h.root.ζ` and the witness as unit times
-- powers of `π`, and cancel in the fraction field to obtain explicit `e`, `n`, and numerator `a`.
-- The maximal-ideal condition gives positive valuation, while the source equation yields
-- `n < p * e` after normalization.  The mixed-characteristic setting in `h.source` ensures
-- `1 - h.root.ζ` is nonzero and belongs to the maximal ideal.  Package the coordinates with
-- `h.root` as `Equation`, retaining
-- `h.root_canonical`.

/-- A finite-level extension has degree `p`. -/
@[stacks 09F4 "finite-level degree bridge"]
theorem finrank_eq
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) : Module.finrank L M = p := (Classical.choose_spec h.2).2.2

/-- A finite-level extension is finite-dimensional. -/
@[stacks 09F4 "finite-dimensionality of a finite-level extension"]
theorem finiteDimensional
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) : FiniteDimensional L M := sorry
-- Proof strategy: apply `RootPresentation.finiteDimensional h.root`; equivalently use positivity of
-- `h.finrank_eq` and the finite-rank criterion.

/-- Every source finite-level extension admits a minimal realized rational level. -/
@[stacks 09F5 "existence of the finite level"]
theorem exists_level
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) : ∃ l : ℚ, IsAtLevel B L M p l := sorry
-- Proof strategy: obtain a canonical finite-level equation from `h.exists_equation`.  Normalize its
-- denominator and minimize `n` with the primitive root, canonical polynomial, and uniformizer
-- fixed.  All uniformizers are associated, so any other uniformizer coordinates for the same
-- primitive root have the same positive exponent `e`.  Natural-number well-ordering therefore
-- gives the minimum among all such coordinate equations.  Package the minimizer
-- as `Presentation` and choose its `level`.

/-- Compatible equivalences preserve finite-level extensions. -/
@[stacks 09F4 "equivalence invariance of finite-level extensions"]
theorem congr
    {B : Type u} [CommRing B] [IsLocalRing B]
    {B' : Type u'} [CommRing B'] [IsLocalRing B']
    {L : Type v} [Field L] [Algebra B L]
    {L' : Type v'} [Field L'] [Algebra B' L']
    {M : Type w} [Field M] [Algebra L M]
    {M' : Type w'} [Field M'] [Algebra L' M']
    {p : ℕ} [Fact p.Prime]
    (eB : B ≃+* B') (eL : L ≃+* L') (eM : M ≃+* M')
    (hBL : eL.toRingHom.comp (algebraMap B L) =
      (algebraMap B' L').comp eB.toRingHom)
    (hLM : eM.toRingHom.comp (algebraMap L M) =
      (algebraMap L' M').comp eL.toRingHom) :
    IsExtension B L M p ↔ IsExtension B' L' M' p := sorry
-- Proof strategy: transport a witnessing root presentation through `eB`, `eL`, and `eM`.  Use
-- `hBL` and `hLM` for the polynomial evaluation and generator equations, `map_polynomial` for
-- canonicity, equivalence invariance of maximal ideals for the source finite-level witness, and
-- linear-equivalence invariance of `Module.finrank`.  Apply the inverse equivalences for the reverse
-- implication.

end IsExtension

namespace IsAtLevel

/-- A realized finite level has a chosen minimal presentation available through a named
noncomputable accessor. -/
@[stacks 09F5 "chosen presentation at a finite level"]
noncomputable def presentation
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    (h : IsAtLevel B L M p l) : Presentation B L M p :=
  Classical.choose h

/-- The chosen presentation realizes the requested rational level. -/
@[stacks 09F5 "level specification of the chosen presentation"]
theorem presentation_level
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    (h : IsAtLevel B L M p l) : l = (h.presentation).level := sorry
-- Proof strategy: unfold `presentation` and project `Classical.choose_spec h`.

/-- An exact-level owner exposes its normalized presentation and level equation. -/
@[stacks 09F5 "finite-level presentation specification"]
theorem exists_presentation
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    (h : IsAtLevel B L M p l) :
    ∃ P : Presentation B L M p, l = P.level := sorry
-- Proof strategy: return the existential statement `h` itself, or choose `h.presentation` together
-- with `h.presentation_level`.

/-- Forgetting the exact rational level gives the underlying finite-level extension. -/
@[stacks 09F5 "forgetting the finite level"]
theorem toExtension
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    (h : IsAtLevel B L M p l) : IsExtension B L M p := sorry
-- Proof strategy: apply `Presentation.isExtension h.presentation`.

/-- An extension at a finite level has degree `p`. -/
@[stacks 09F5 "finite-level degree bridge"]
theorem finrank_eq
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    (h : IsAtLevel B L M p l) : Module.finrank L M = p := sorry
-- Proof strategy: return the degree field of `h.presentation`.

/-- An extension at a finite level is finite-dimensional. -/
@[stacks 09F5 "finite-dimensionality at a finite level"]
theorem finiteDimensional
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    (h : IsAtLevel B L M p l) : FiniteDimensional L M := sorry
-- Proof strategy: apply `Presentation.finiteDimensional h.presentation`.

/-- Every realized finite level is nonnegative. -/
@[stacks 09F5 "nonnegativity of a realized finite level"]
theorem nonneg
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    (h : IsAtLevel B L M p l) : 0 ≤ l := sorry
-- Proof strategy: rewrite `l` with `h.presentation_level` and apply
-- `Presentation.level_nonneg h.presentation`.

/-- Every realized finite level is strictly below `p`. -/
@[stacks 09F5 "upper bound for a realized finite level"]
theorem lt_prime
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    (h : IsAtLevel B L M p l) : l < p := sorry
-- Proof strategy: rewrite `l` with `h.presentation_level` and apply
-- `Presentation.level_lt h.presentation`.

/-- Exact finite levels are unique for a fixed extension. -/
@[stacks 09F5 "uniqueness of an exact finite level"]
theorem unique
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l l' : ℚ} [Fact p.Prime]
    (hl : IsAtLevel B L M p l) (hl' : IsAtLevel B L M p l') : l = l' := sorry
-- Proof strategy: rewrite both levels using their chosen presentations and apply
-- `Presentation.level_eq`.

/-- Compatible equivalences preserve an exact finite level. -/
@[stacks 09F5 "equivalence invariance at a finite level"]
theorem congr
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {B' : Type u'} [CommRing B'] [IsDomain B'] [IsDiscreteValuationRing B']
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {L' : Type v'} [Field L'] [Algebra B' L'] [IsFractionRing B' L']
    {M : Type w} [Field M] [Algebra L M]
    {M' : Type w'} [Field M'] [Algebra L' M']
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    (eB : B ≃+* B') (eL : L ≃+* L') (eM : M ≃+* M')
    (hBL : eL.toRingHom.comp (algebraMap B L) =
      (algebraMap B' L').comp eB.toRingHom)
    (hLM : eM.toRingHom.comp (algebraMap L M) =
      (algebraMap L' M').comp eL.toRingHom) :
    IsAtLevel B L M p l ↔ IsAtLevel B' L' M' p l := sorry
-- Proof strategy: transport the chosen minimal presentation across the three compatible
-- equivalences as in `IsExtension.congr`.  The denominator exponents and therefore the rational
-- level are unchanged; transport the minimality inequality in both directions.  Use the inverse
-- equivalences for the converse.

end IsAtLevel

end FiniteLevel
end KummerArtinSchreier
