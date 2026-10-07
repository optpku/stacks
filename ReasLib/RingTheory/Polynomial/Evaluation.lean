module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Eventual evaluation of polynomials

This neutral leaf contains uniqueness from agreement on an eventual natural-number tail.  It is
independent of numerical polynomials and can be reused by Hilbert and growth arguments alike.
-/

@[expose] public section

universe u

open Filter

namespace Polynomial

/-- A polynomial `P` eventually represents a sequence `f` when their evaluations agree on a
natural-number tail. -/
@[stacks 09CA "eventual polynomial representation"]
def EventuallyEqNat {R : Type u} [Semiring R] (P : Polynomial R) (f : ℕ → R) : Prop :=
  ∀ᶠ n : ℕ in atTop, P.eval (n : R) = f n

/-- A polynomial `P` eventually represents an integer-indexed function `f` when their evaluations
agree on an integer tail. -/
def EventuallyEqInt {R : Type u} [Ring R] (P : Polynomial R) (f : ℤ → R) : Prop :=
  ∀ᶠ n : ℤ in atTop, P.eval (n : R) = f n

/-- For an integer function obtained from a natural sequence by `Int.toNat`, integer-tail and
natural-tail polynomial representation are equivalent. -/
theorem eventuallyEqInt_iff_eventuallyEqNat {R : Type u} [Ring R]
    {P : Polynomial R} {f : ℕ → R} :
    P.EventuallyEqInt (fun n : ℤ ↦ f n.toNat) ↔ P.EventuallyEqNat f := sorry

/-- Eventual natural-tail representations are closed under a difference of
three polynomial/function pairs. -/
theorem EventuallyEqNat.sub_sub {R : Type u} [Ring R]
    {P Q T : Polynomial R} {f g h : ℕ → R}
    (hP : P.EventuallyEqNat f) (hQ : Q.EventuallyEqNat g)
    (hT : T.EventuallyEqNat h) :
    (P - Q - T).EventuallyEqNat (fun n ↦ f n - g n - h n) := sorry

/-- A selected polynomial eventually representing `f`, when such a polynomial exists, and `0`
otherwise. The definition is independent of any proof of existence; uniqueness is asserted only
under the characteristic-zero domain hypotheses below. -/
@[stacks 09CA "selected eventual polynomial representative"]
noncomputable def eventualRepresentative {R : Type u} [Semiring R]
    (f : ℕ → R) : Polynomial R :=
  @dite (Polynomial R) (∃ P : Polynomial R, P.EventuallyEqNat f)
    (Classical.propDecidable _) (fun h ↦ Classical.choose h) (fun _ ↦ 0)

/-- If `f` has an eventual polynomial representative, `eventualRepresentative f` is one. -/
theorem eventualRepresentative_spec {R : Type u} [Semiring R] {f : ℕ → R}
    (hf : ∃ P : Polynomial R, P.EventuallyEqNat f) :
    (eventualRepresentative f).EventuallyEqNat f := sorry

/-- The totalized selected polynomial is a genuine eventual representative exactly when an
eventual representative exists. -/
theorem eventualRepresentative_eventuallyEqNat_iff {R : Type u} [Semiring R] {f : ℕ → R} :
    (eventualRepresentative f).EventuallyEqNat f ↔
      ∃ P : Polynomial R, P.EventuallyEqNat f := sorry

/-- Over a characteristic-zero domain, eventual agreement on natural-number evaluations forces
two polynomials to be equal. -/
theorem eq_of_eventuallyEq_eval_nat {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    {P Q : Polynomial R}
    (h : ∀ᶠ n : ℕ in atTop, P.eval (n : R) = Q.eval (n : R)) :
    P = Q := sorry

/-- Over a characteristic-zero domain, every eventual representative is the canonical one. -/
theorem eq_eventualRepresentative {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    {f : ℕ → R} {P : Polynomial R} (hP : P.EventuallyEqNat f) :
    P = eventualRepresentative f := sorry

/-- Over a characteristic-zero domain, eventual representation is characterized by equality with
the canonical representative, provided a representative exists. -/
theorem eventuallyEqNat_iff_eq_eventualRepresentative
    {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    {f : ℕ → R} (hf : ∃ P : Polynomial R, P.EventuallyEqNat f) (P : Polynomial R) :
    P.EventuallyEqNat f ↔ P = eventualRepresentative f := sorry

end Polynomial
