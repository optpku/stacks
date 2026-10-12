/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import ReasLib.RingTheory.Derivation.RegularQuotient
public import ReasLib.RingTheory.RegularLocalRing.SerreCondition
public import ReasLib.RingTheory.Smooth.Regularity.RegularBase
import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular hypersurfaces controlled by a derivation

@stack 07PG
-/

@[expose] public section

open Polynomial PolynomialModule

universe u

namespace Derivation

variable {R : Type u} [CommRing R] [IsRegularRing R] {f : R}

/-- Lemma 15.48.4: if an absolute derivation sends `f` to a unit, then every hypersurface
`p(z) - f` with `p : Polynomial ℤ` defines a regular `AdjoinRoot`. -/
@[stacks 07PG "regularity of a derivation-controlled hypersurface"]
theorem isRegularRing_adjoinRoot_sub_C_of_isUnit
    (D : Derivation ℤ R R) (hDf : IsUnit (D f)) (p : Polynomial ℤ) :
    IsRegularRing (AdjoinRoot (p.map (Int.castRingHom R) - C f)) := sorry

/-- Lemma 15.48.4: the existence of an absolute derivation sending `f` to a unit implies
regularity of every hypersurface `p(z) - f`. -/
@[stacks 07PG "regularity from a unit-valued derivation"]
theorem isRegularRing_adjoinRoot_sub_C_of_exists
    (hD : ∃ D : Derivation ℤ R R, IsUnit (D f)) (p : Polynomial ℤ) :
    IsRegularRing (AdjoinRoot (p.map (Int.castRingHom R) - C f)) := sorry

end Derivation
