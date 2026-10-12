/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.Away.Relative

/-!
# Principal-Open Product Splittings at a Prime

This leaf owns the algebraic form of the local product decomposition: a
finitely presented algebra whose map on selected local rings is bijective
splits, after shrinking by one element outside the base prime, into the base
localization and a complementary algebra.  The result is independent of any
chosen polynomial presentation or proof-specific zero-section construction.

@stack 00QR
-/

@[expose] public section

universe u v

namespace Algebra.FinitePresentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]

/-- Tag `00QR`: if a finitely presented `R`-algebra induces a bijection on
the local rings at primes `p` and `q` lying over one another, then after
shrinking away from `p` it is a product of the base chart and another
`R_f`-algebra. -/
@[stacks 00QR "principal-open local product decomposition"]
theorem exists_away_product_of_localRingHom_bijective
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over)) :
    ∃ (f : R) (_ : f ∉ p),
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        Localization.Away.Relative.algebraMapAlgebra f
      ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra (Localization.Away f) C),
        Nonempty
          (Localization.Away (algebraMap R S f) ≃ₐ[Localization.Away f]
            (Localization.Away f × C)) := sorry

end Algebra.FinitePresentation
