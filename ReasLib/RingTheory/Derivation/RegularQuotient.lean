/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.Ideal.Principal
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular principal quotients detected by derivations

A derivation whose value on a generator is a unit modulo that generator detects regularity of the
corresponding principal quotient.

@stack 07PF
-/

@[expose] public section

universe u

namespace Derivation

variable {R : Type u} [CommRing R] [IsRegularRing R] {f : R}

/-- Primitive form of Lemma 15.48.2: a derivation taking `f` to a unit modulo `(f)` makes the
principal quotient regular. -/
@[stacks 07PF "regular principal quotient from a derivation"]
theorem isRegularRing_quotient_principalIdeal_of_isUnit (D : Derivation ℤ R R)
    (hDf : IsUnit (Ideal.Quotient.mk (principalIdeal f) (D f))) :
    IsRegularRing (R ⧸ principalIdeal f) := sorry

/-- Lemma 15.48.2: if some derivation takes `f` to a unit modulo `(f)`, then the principal
quotient `R ⧸ (f)` is regular. -/
@[stacks 07PF "Lemma 15.48.2"]
theorem isRegularRing_quotient_principalIdeal_of_exists
    (hD : ∃ D : Derivation ℤ R R,
      IsUnit (Ideal.Quotient.mk (principalIdeal f) (D f))) :
    IsRegularRing (R ⧸ principalIdeal f) := sorry

end Derivation
