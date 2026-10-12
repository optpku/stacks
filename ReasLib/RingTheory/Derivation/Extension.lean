/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extending derivations

Absolute derivations extend uniquely to adic completions and localizations.  A derivation also
extends across a finite-type algebra after multiplying by a sufficiently large power whenever an
away localization identifies the two rings.

@stack 07PE
-/

@[expose] public section

open scoped RightActions

universe u v

namespace Derivation.Extension

variable {R : Type u} [CommRing R]

/-- Lemma 15.48.1 (1): an absolute derivation of `R` has a unique extension to the `I`-adic
completion of `R`. -/
@[stacks 07PE "Lemma 15.48.1 (1)"]
theorem existsUnique_adicCompletion (D : Derivation ℤ R R) (I : Ideal R) :
    ∃! Dhat : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
      Dhat.compAlgebraMap R =
        (Algebra.linearMap R (AdicCompletion I R)).compDer D := sorry

/-- Lemma 15.48.1 (2): an absolute derivation of `R` has a unique extension to any localization
of `R` at `S`. -/
@[stacks 07PE "Lemma 15.48.1 (2)"]
theorem existsUnique_localization (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    ∃! Dloc : Derivation ℤ A A,
      Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D := sorry

/-- Lemma 15.48.1 (3): for a finite-type `R`-algebra `R'`, if the away localizations at `g`
are isomorphic and the image of `g` is a nonzerodivisor, then `g ^ N • D` extends to `R'` for
some `N`. -/
@[stacks 07PE "Lemma 15.48.1 (3)"]
theorem exists_pow_smul_of_finiteType_awayIso
    (D : Derivation ℤ R R) {R' : Type v} [CommRing R'] [Algebra R R']
    [Algebra.FiniteType R R'] (g : R)
    (eAway : Localization.Away g ≃ₐ[R] Localization.Away (algebraMap R R' g))
    (hg : IsRegular (algebraMap R R' g)) :
    ∃ N : ℕ, ∃ D' : Derivation ℤ R' R',
      D'.compAlgebraMap R = (Algebra.linearMap R R').compDer (g ^ N • D) := sorry

end Derivation.Extension
