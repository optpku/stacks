/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

open Polynomial

universe u

namespace AdjoinRoot

/-- For coprime `a` and `b` in a commutative ring, finite order of the image of
`a` modulo `Ideal.span {b}` yields a monic root extension in which
`algebraMap A (AdjoinRoot p) a - algebraMap A (AdjoinRoot p) b * root p` is a
unit and the canonical map from `A` is injective. -/
theorem existsMonogenicUnitExtension
    {A : Type u} [CommRing A] (a b : A) (h_coprime : IsCoprime a b)
    (h_root : IsOfFinOrder (Ideal.Quotient.mk (Ideal.span {b}) a)) :
    ∃ (p : Polynomial A) (h_monic : p.Monic),
      Function.Injective (algebraMap A (AdjoinRoot p)) ∧
        IsUnit (algebraMap A (AdjoinRoot p) a -
          algebraMap A (AdjoinRoot p) b * AdjoinRoot.root p) := sorry

end AdjoinRoot

end
