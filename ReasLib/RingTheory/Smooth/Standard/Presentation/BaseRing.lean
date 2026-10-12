/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Standard.Element.Fin

/-!
# Base-ring form of strict-standard tail conditions

The presentation-intrinsic tail condition is the reusable owner.  This leaf
provides the source-facing rewrite for an element lifted from the base ring.
-/

@[expose] public section

open Algebra

universe u v

namespace Algebra.Presentation

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {n m c : ℕ}

namespace TailRelationCondition

/-- For a base element `π`, the intrinsic tail condition is equivalent to the
literal equation using `algebraMap R P.Ring π`. -/
@[stacks 07CS]
theorem iff_baseRing
    (P : Presentation R A (Fin n) (Fin m))
    (π : R) (hcₘ : c ≤ m) :
    P.tailRelationCondition (algebraMap R A π) hcₘ ↔
      ∀ j : Fin (m - c),
        algebraMap R P.Ring π *
            P.relation (Fin.natAdd_castLEEmb (Nat.sub_le m c) j) ∈
          P.leadingRelationIdeal hcₘ + P.ker ^ 2 := sorry

end TailRelationCondition

end Algebra.Presentation

namespace Algebra.IsStrictlyStandard.Presentation

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {π : R}

/-- Lemma 16.7.1.1 (tag 07CS): strict standardness of the image of a base element has a finite
presentation witness whose tail condition is written with the literal base-ring lift. -/
@[stacks 07CS]
theorem exists_baseRing_tail
    (hπ : IsStrictlyStandard R (algebraMap R A π)) :
    ∃ (n m : ℕ) (P : Algebra.Presentation R A (Fin n) (Fin m))
        (c : ℕ) (hcₘ : c ≤ m),
      ∀ j : Fin (m - c),
        algebraMap R P.Ring π *
            P.relation (Fin.natAdd_castLEEmb (Nat.sub_le m c) j) ∈
          P.leadingRelationIdeal hcₘ + P.ker ^ 2 := sorry

end Algebra.IsStrictlyStandard.Presentation
