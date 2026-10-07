module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.FixedPoints
public import ReasLib.RingTheory.Invariant.FixedPoints.Subalgebra
public import ReasLib.RingTheory.Invariant.Prime

@[expose] public section

/-!
# Prime fibers of fixed subalgebras

This leaf specializes finite invariant prime-fiber uniqueness to a fixed subalgebra and to an
extension between nested fixed subalgebras.  The results depend only on finite subgroup actions;
normality and Galois-faithfulness assumptions belong to stronger downstream applications.
@stack 0BU6
-/

open scoped Pointwise

universe u v w

namespace FixedPoints

section Subring

variable {B : Type v} {G : Type w}
variable [CommRing B] [Group G] [Finite G] [MulSemiringAction G B]

/-- A stable prime is the unique prime over its contraction to the fixed-point subring. -/
@[stacks 0BU6 "finite invariant prime fiber uniqueness over a fixed subring"]
theorem primesOver_under_eq_singleton_of_isStable
    (m : Ideal B) [m.IsPrime] (hfix : m.IsStable G) :
    (m.under (FixedPoints.subring B G)).primesOver B = {m} := sorry

-- Proof strategy: specialize
-- `Algebra.IsInvariant.primesOver_under_eq_singleton_of_isStable` to the canonical invariant
-- extension `FixedPoints.subring B G → B` and the supplied stability hypothesis.

end Subring

section Subalgebra

variable {A : Type u} {B : Type v} {G : Type w}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

section StableAction

variable {H : Type w} [Group H] [Finite H] [MulSemiringAction H B] [SMulCommClass H A B]

/-- A finite stable action has a singleton prime fiber over the fixed-subalgebra contraction. -/
@[stacks 0BU6 "prime fiber of a finite stable fixed-subalgebra action"]
theorem primesOver_under_eq_singleton_of_isStable_subalgebra
    (m : Ideal B) [m.IsPrime] (hfix : m.IsStable H) :
    (m.under (FixedPoints.subalgebra A B H)).primesOver B = {m} := sorry

-- Proof strategy: apply the generic invariant prime-fiber singleton theorem using
-- `FixedPoints.subalgebra_isInvariant`; the fixed-subalgebra algebra map is the ambient subtype
-- inclusion, so its contraction is definitionally the displayed `under`.

end StableAction

end Subalgebra

section SubalgebraFacade

variable {A : Type u} {B : Type v} {G : Type w}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- If a subgroup stabilizes a prime, that prime is the unique ambient prime over its
contraction to the subgroup fixed subalgebra. -/
@[stacks 0BU6 "prime fiber over a fixed-subalgebra contraction"]
theorem primesOver_under_eq_singleton
    (H : Subgroup G) [Finite H] (m : Ideal B) [m.IsPrime]
    (hfix : H ≤ MulAction.stabilizer G m) :
    (m.under (FixedPoints.subalgebra A B H)).primesOver B = {m} := sorry

-- Proof strategy: convert `hfix` to stability of `m` under the restricted `H`-action with
-- `Ideal.isStable_subgroup_iff_le_stabilizer`, then apply
-- `primesOver_under_eq_singleton_of_isStable_subalgebra`.

/-- For `H ≤ H'`, if `H'` stabilizes a prime, its contraction to `B ^ H` is the unique prime
over its contraction to `B ^ H'`. -/
@[stacks 0BU6 "prime fiber between nested fixed subalgebras"]
theorem primesOver_under_eq_singleton_of_le
    {H H' : Subgroup G} (h : H ≤ H') [Finite H']
    (m : Ideal B) [m.IsPrime] (hfix : H' ≤ MulAction.stabilizer G m) :
    -- Local instance justification (defeq pin): the prime fiber must use the canonical inclusion
    -- algebra selected by `subalgebraAlgebraOfLe h`.
    letI : Algebra (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) :=
      FixedPoints.subalgebraAlgebraOfLe h
    (m.under (FixedPoints.subalgebra A B H')).primesOver
        (FixedPoints.subalgebra A B H) =
      {m.under (FixedPoints.subalgebra A B H)} := sorry

-- Proof strategy: take a prime of `B ^ H` over the `H'`-fixed contraction and lift it to a prime
-- of `B` using integrality of `B / B ^ H`.  Its contraction to `B ^ H'` is the displayed one, so
-- `primesOver_under_eq_singleton H' m hfix` forces the lift to be `m`; contract back to `B ^ H`.

end SubalgebraFacade

end FixedPoints
