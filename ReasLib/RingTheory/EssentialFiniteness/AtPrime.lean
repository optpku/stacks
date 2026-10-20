/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Local.AtPrime

@[expose] public section

/-!
# Finite Presentation Near a Prime

This leaf gives the algebra-side form of the principal-open finite-presentation
condition owned generically by `RingHom.FinitePresentationAt`.  It is kept
separate from the ring-hom leaf because statements about `Algebra.SmoothAtPrime`
naturally use the ambient algebra form.

@stack 00TF
-/

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- The `R`-algebra `S` is of finite presentation near `q` when it is of finite
presentation after inverting one element outside `q`. -/
@[stacks 00TF "finite presentation near a prime"]
def FinitePresentationAt (q : PrimeSpectrum S) : Prop :=
  (algebraMap R S).FinitePresentationAt q

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The algebra-side finite-presentation-at-a-prime predicate is exactly the
principal-open neighborhood condition. -/
@[stacks 00TF "finite presentation near a prime"]
theorem finitePresentationAt_iff (q : PrimeSpectrum S) :
    FinitePresentationAt R S q ↔
      ∃ g : S, g ∉ q.asIdeal ∧ Algebra.FinitePresentation R (Localization.Away g) := sorry

namespace FinitePresentationAt

/-- A finitely presented algebra is of finite presentation near every target
prime. -/
@[stacks 00TF "finite presentation near a prime"]
theorem of_finitePresentation [Algebra.FinitePresentation R S] (q : PrimeSpectrum S) :
    FinitePresentationAt R S q := sorry

end FinitePresentationAt

end Algebra
