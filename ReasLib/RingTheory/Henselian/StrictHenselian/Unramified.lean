/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Criteria
public import ReasLib.RingTheory.Henselian.Finite
public import ReasLib.RingTheory.Henselian.StrictHenselian
public import ReasLib.RingTheory.Unramified.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Unramified algebras over strictly henselian local rings

This leaf packages the finite-part decomposition of an unramified algebra over
a strictly henselian local ring.  It reuses the common finite-part and finite
product data owners.

@stack 04GL
-/

@[expose] public section

open IsLocalRing

universe u v

namespace StrictHenselianLocalRing.Unramified

/-- Lemma 10.153.8: an unramified algebra over a strictly henselian local ring
splits into finite local factors with surjective structure maps and a remainder
having no point over the closed point. -/
@[stacks 04GL "unramified finite-part decomposition"]
theorem existsFinitePartDecomposition
    {R : Type u} {S : Type v} [CommRing R] [StrictHenselianLocalRing R]
    [CommRing S] [Algebra R S] [Algebra.Unramified R S] :
    ∃ D : Algebra.FinitePartDecomposition R S,
      ∃ E : HenselianLocalRing.FiniteProduct R D.finitePart,
        (∀ i, Function.Surjective (algebraMap R (E.factor i))) ∧
          ∀ q : PrimeSpectrum D.remainder,
            Ideal.comap (algebraMap R D.remainder) q.asIdeal ≠ maximalIdeal R := sorry

end StrictHenselianLocalRing.Unramified
