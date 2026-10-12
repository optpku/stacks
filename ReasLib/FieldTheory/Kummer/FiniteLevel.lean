/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RootsOfUnity.KummerArtinSchreier
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
system whose rational ratio is globally minimal.  Thus the root-theoretic definition, the
valuation computation, and the exact level invariant remain separate reusable layers.

@stack 09F4
@stack 09F5
-/

/-- One generating Kummer--Artin--Schreier equation with explicit denominator data. -/
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

/-- The source finite-level condition: the chosen uniformizer denominator has order strictly smaller
than the order contributed by the `p`th power of `1 - ζ`. -/
@[stacks 09F4 "finite-level denominator bound"]
def Equation.IsFiniteLevel
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
  (h : Equation B L M p) : Prop :=
  Irreducible h.π ∧ h.n < p * h.e

/-- The displayed polynomial is the canonical quotient polynomial attached to `ζ`. -/
@[stacks 09F4 "canonical polynomial condition on a denominator equation"]
def Equation.IsCanonical
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) : Prop :=
  h.P = KummerArtinSchreier.polynomial p h.ζ

/-- A finite-level presentation.  Its denominator satisfies the source bound and its rational level
is minimal among all finite-level equations generating the same extension. -/
@[stacks 09F4 "Kummer--Artin--Schreier finite-level presentation"]
structure Presentation
    (B : Type u) [CommRing B]
    (L : Type v) [Field L] [Algebra B L]
    (M : Type w) [Field M] [Algebra L M]
    (p : ℕ) extends Equation B L M p where
  /-- The chosen denominator presentation satisfies the finite-level bound. -/
  finiteLevel : toEquation.IsFiniteLevel
  /-- The displayed polynomial is the canonical quotient polynomial. -/
  canonical : toEquation.IsCanonical
  /-- The displayed root generates a degree-`p` extension. -/
  degreeP : Module.finrank L M = p
  /-- The chosen denominator ratio is minimal among canonical finite-level equations. -/
  minimal :
    ∀ Q : Equation B L M p,
      Q.IsCanonical → Q.IsFiniteLevel → toEquation.level ≤ Q.level

/-- The level of a minimal finite-level presentation. -/
@[stacks 09F5 "level of a finite-level presentation"]
abbrev Presentation.level
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Presentation B L M p) : ℚ := h.toEquation.level

/-- A degree-`p` extension is of finite level when it has a generating canonical
Kummer--Artin--Schreier root equation for which `(1 - ζ) ^ p * ξ` comes from the maximal ideal. -/
@[stacks 09F4 "Kummer--Artin--Schreier finite-level extension"]
def IsExtension
    (B : Type u) [CommRing B] [IsLocalRing B]
    (L : Type v) [Field L] [Algebra B L]
    (M : Type w) [Field M] [Algebra L M]
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ h : RootPresentation B L M p,
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
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) (hh : h.IsFiniteLevel) : Irreducible h.π := sorry
-- Proof strategy: unfold `Equation.IsFiniteLevel` and project its first component.

/-- The finite-level condition exposes the strict denominator bound. -/
@[stacks 09F4 "strict finite-level denominator bound"]
theorem n_lt
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) (hh : h.IsFiniteLevel) : h.n < p * h.e := sorry
-- Proof strategy: unfold `Equation.IsFiniteLevel` and project its second component.

/-- A finite-level denominator equation satisfies the uniformizer-free source condition. -/
@[stacks 09F4 "denominator equation to source finite-level condition"]
theorem root_isFiniteLevel
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Equation B L M p) (hh : h.IsFiniteLevel) : h.root.IsFiniteLevel := sorry
-- Proof strategy: use `h.associated` to write `1 - h.ζ` as a unit times `h.π ^ h.e` and combine
-- this with `h.denominator_eq`.  Since `h.n < p * h.e`, cancellation leaves a positive power of
-- the irreducible uniformizer `h.π`; choose the resulting element of `B` as the source witness and
-- prove its maximal-ideal membership via the DVR principal-maximal-ideal criterion.

/-- A finite-level denominator equation gives the source finite-level extension property. -/
@[stacks 09F4 "denominator equation to finite-level extension"]
theorem isExtension
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Equation B L M p) (hc : h.IsCanonical) (hh : h.IsFiniteLevel)
    (hdeg : Module.finrank L M = p) :
    IsExtension B L M p := sorry
-- Proof strategy: choose `h.root` in the existential defining `IsExtension` and supply `hc`,
-- `h.root_isFiniteLevel hh`, and `hdeg`.

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

/-- A finite-level presentation exposes the strict denominator bound defining finite level. -/
@[stacks 09F4 "finite-level bound of a presentation"]
theorem isFiniteLevel
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Presentation B L M p) : h.toEquation.IsFiniteLevel := sorry
-- Proof strategy: return the structure field `h.finiteLevel`.

/-- Minimality forces a positive denominator presentation to have unit numerator. -/
@[stacks 09F5 "normalization of a minimal finite-level presentation"]
theorem isNormalized
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Presentation B L M p) : h.toEquation.IsNormalized := sorry
-- Proof strategy: if `h.n = 0`, use the first normalization branch.  Otherwise, assume the
-- numerator is not a unit.  In the DVR factor it by the uniformizer `h.π`, decrease the denominator
-- exponent accordingly, and build another canonical finite-level equation with strictly smaller
-- rational level, contradicting `h.minimal`.

/-- A presentation canonically gives the corresponding finite-level extension property. -/
@[stacks 09F4 "presentation to finite-level extension"]
theorem isExtension
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : IsExtension B L M p := sorry
-- Proof strategy: apply `Equation.isExtension` to `h.toEquation`, using `h.canonical`,
-- `h.finiteLevel`, and `h.degreeP`.

/-- A presentation realizes its own exact level. -/
@[stacks 09F5 "presentation at its rational level"]
theorem isAtLevel
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : IsAtLevel B L M p h.level := sorry
-- Proof strategy: choose `h` in the existential defining `IsAtLevel` and use reflexivity for its
-- level equation.

/-- A presentation exposes the quotient-polynomial property of its displayed polynomial. -/
@[stacks 09F4 "finite-level presentation quotient polynomial"]
theorem quotient
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Presentation B L M p) :
    KummerArtinSchreier.IsQuotient p h.ζ h.P := sorry
-- Proof strategy: apply `Equation.quotient h.toEquation`.

/-- The canonical polynomial attached to a presentation is a quotient polynomial. -/
@[stacks 09F4 "canonical finite-level presentation quotient polynomial"]
theorem canonical_quotient
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) :
    KummerArtinSchreier.IsQuotient p h.ζ (KummerArtinSchreier.polynomial p h.ζ) := sorry
-- Proof strategy: apply `Equation.canonical_quotient h.toEquation h.canonical`.

/-- A presentation is minimal among all finite-level equations generating the same extension. -/
@[stacks 09F5 "minimality of a finite-level presentation"]
theorem level_le
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Presentation B L M p) (Q : Equation B L M p)
    (hQ : Q.IsCanonical) (hFinite : Q.IsFiniteLevel) : h.level ≤ Q.level := sorry
-- Proof strategy: apply the structure field `h.minimal Q hQ hFinite`.

/-- Any two minimal finite-level presentations of the same extension have the same level. -/
@[stacks 09F5 "uniqueness of the finite level"]
theorem level_eq
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (P Q : Presentation B L M p) : P.level = Q.level := sorry
-- Proof strategy: apply `P.level_le` to `Q.toEquation` and conversely `Q.level_le` to
-- `P.toEquation`, then use antisymmetry.

/-- The level of a presentation is nonnegative. -/
@[stacks 09F5 "nonnegativity of a finite level"]
theorem level_nonneg
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ}
    (h : Presentation B L M p) : 0 ≤ h.level := sorry
-- Proof strategy: unfold `Presentation.level` and `Equation.level`; the numerator `h.n` is
-- nonnegative and the denominator `h.e` is positive by `h.e_pos`, so rational division is
-- nonnegative.

/-- A finite level lies strictly below the prime degree. -/
@[stacks 09F5 "upper bound for a finite level"]
theorem level_lt
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : h.level < p := sorry
-- Proof strategy: rewrite the rational inequality as `h.n < p * h.e` using positivity of `h.e`,
-- then apply `h.finiteLevel.2` and cast the natural-number inequality to `ℚ`.

/-- A degree-`p` presentation supplies finite-dimensionality without requiring it as ambient input. -/
@[stacks 09F4 "finite-dimensionality from a finite-level presentation"]
theorem finiteDimensional
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : Presentation B L M p) : FiniteDimensional L M := sorry
-- Proof strategy: apply `Equation.finiteDimensional h.toEquation`.

end Presentation

namespace IsExtension

/-- The generating root presentation chosen from a source finite-level extension. -/
@[stacks 09F4 "chosen root of a finite-level extension"]
noncomputable def root
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) : RootPresentation B L M p :=
  Classical.choose h

/-- The chosen root uses the canonical polynomial attached to its primitive root. -/
@[stacks 09F4 "canonical polynomial of the chosen finite-level root"]
theorem root_canonical
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) :
    h.root.P = KummerArtinSchreier.polynomial p h.root.ζ := sorry
-- Proof strategy: unfold `root` and project the first component of `Classical.choose_spec h`.

/-- The chosen root satisfies the uniformizer-free source finite-level condition. -/
@[stacks 09F4 "source condition of the chosen finite-level root"]
theorem root_isFiniteLevel
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) : h.root.IsFiniteLevel := sorry
-- Proof strategy: unfold `root` and project the second component of `Classical.choose_spec h`.

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
        Q.IsFiniteLevel ∧ Module.finrank L M = p := sorry
-- Proof strategy: this is exactly the existential defining `IsExtension`; return `h` (or choose
-- `h.root` and its three named specification theorems).

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
-- `n < p * e`.  Package these coordinates with `h.root` as `Equation`, retaining
-- `h.root_canonical`.

/-- A finite-level extension has degree `p`. -/
@[stacks 09F4 "finite-level degree bridge"]
theorem finrank_eq
    {B : Type u} [CommRing B] [IsLocalRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    (h : IsExtension B L M p) : Module.finrank L M = p := sorry
-- Proof strategy: project the final component of `Classical.choose_spec h` for `h.root`.

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
-- denominator and minimize the discrete valuation ratio `n / e` among all canonical finite-level
-- equations, using well-foundedness of the natural valuation coordinates.  Package the minimizer
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
