/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.IntegralClosure
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.TotalRamification
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Prescribed uniformizers in totally ramified extensions

This file owns the source-facing uniformizer data attached to a finite totally ramified extension
of a DVR.  The equations are bundled around one distinguished target uniformizer, while the
existence theorem keeps the field extension and normalization canonical.

@stack 09EW
-/

open Ideal IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v

namespace DVR

section Congruence

variable (A : Type u) (B : Type v)
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

/-- Uniformizer data realizing the two congruence formulas used in a prescribed totally ramified
extension. -/
@[stacks 09EW "prescribed ramified uniformizer data"]
structure UniformizerCongruence (π : A) (n q : ℕ) where
  /-- The distinguished uniformizer of the target DVR. -/
  uniformizer : B
  /-- The correction coefficient measured using the source power `π ^ n`. -/
  sourceCorrection : B
  /-- The correction coefficient measured using the target uniformizer. -/
  targetCorrection : B
  /-- The ramification index is the prescribed integer `q`. -/
  ramificationIndex_eq : ramificationIndex A B = q
  /-- The distinguished element generates the target maximal ideal. -/
  maximalIdeal_eq : maximalIdeal B = Ideal.span ({uniformizer} : Set B)
  /-- The first prescribed congruence formula. -/
  pow_eq_source :
    uniformizer ^ q = algebraMap A B π + algebraMap A B (π ^ n) * sourceCorrection
  /-- The second prescribed congruence formula. -/
  pow_eq_target :
    uniformizer ^ q = algebraMap A B π + uniformizer ^ (n * q) * targetCorrection

namespace UniformizerCongruence

/-- The four properties carried by prescribed uniformizer data. -/
@[stacks 09EW "prescribed uniformizer specification"]
theorem spec {π : A} {n q : ℕ} (h : UniformizerCongruence A B π n q) :
    ramificationIndex A B = q ∧
      maximalIdeal B = Ideal.span ({h.uniformizer} : Set B) ∧
      h.uniformizer ^ q =
        algebraMap A B π + algebraMap A B (π ^ n) * h.sourceCorrection ∧
      h.uniformizer ^ q =
        algebraMap A B π + h.uniformizer ^ (n * q) * h.targetCorrection := sorry
-- Proof strategy: assemble the conjunction directly from `h.ramificationIndex_eq`,
-- `h.maximalIdeal_eq`, `h.pow_eq_source`, and `h.pow_eq_target`.

/-- Prescribed uniformizer data exist exactly when the three elements and their four defining
properties exist. -/
@[stacks 09EW "prescribed uniformizer existence characterization"]
theorem nonempty_iff {π : A} {n q : ℕ} :
    Nonempty (UniformizerCongruence A B π n q) ↔
      ∃ πB b b' : B,
        ramificationIndex A B = q ∧
          maximalIdeal B = Ideal.span ({πB} : Set B) ∧
          πB ^ q = algebraMap A B π + algebraMap A B (π ^ n) * b ∧
          πB ^ q = algebraMap A B π + πB ^ (n * q) * b' := sorry
-- Proof strategy: unpack a `UniformizerCongruence` into its three data fields and four law fields
-- in the forward direction; in the reverse direction construct the structure from the displayed
-- witnesses and conjunction projections.

end UniformizerCongruence

end Congruence

namespace Field

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]

/-- A `p`-power degree and a chosen base uniformizer can be realized by a finite separable totally
ramified extension whose normalization carries the two prescribed uniformizer congruences. -/
@[stacks 09EW "totally ramified extension with prescribed uniformizer"]
theorem exists_totallyRamified_with_uniformizer
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n q : ℕ} (hn : 1 < n) (hq : ∃ m : ℕ, q = p ^ m) :
    ∃ (L : Type (max u v)) (_ : Field L) (_ : Algebra A L)
      (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L)
      (_ : FiniteDimensional (FractionRing A) L)
      (_ : Algebra.IsSeparable (FractionRing A) L)
      (_ : IsTotallyRamified A (FractionRing A) L)
      (_ : IsDiscreteValuationRing (integralClosure A L))
      (_ : IsExtensionOfDiscreteValuationRings A (integralClosure A L)),
      Module.finrank (FractionRing A) L = q ∧
        Nonempty (UniformizerCongruence A (integralClosure A L) π n q) := sorry
-- Proof strategy: split on `q = 1` and on `CharZero (FractionRing A)`.  For `q = 1`, use the
-- trivial fraction-field extension and zero correction coefficients.  In mixed characteristic,
-- use the Eisenstein extension defined by `X ^ q - π`, transport its root ring to the integral
-- closure, and apply the uniformizer-root finrank, total-ramification, and ramification-index API.
-- In equal characteristic, use the separable additive polynomial
-- `X ^ q - π ^ (n + q - 1) * X - π`; prove that its root ring is a DVR with maximal ideal
-- generated by the distinguished root, identify its fraction field and normalization, and read
-- the two correction formulas from the defining equation and the ramification-index calculation.

end

end Field

end DVR
