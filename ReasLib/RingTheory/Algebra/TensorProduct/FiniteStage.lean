module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Adjoin.FGBaseChange
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely Generated Tensor Stages

This leaf records the finite-stage descent intrinsic to tensor products of
algebras over a field.  The primary object is a pair of finitely generated
subalgebras and its canonical map into the ambient tensor product.  The
source-facing reducedness, zero-divisor, and idempotent consequences are
separate propositions, so later users can reuse the underlying finite-stage
API without inheriting a particular obstruction.

@stack 00I3
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

/-- Tag 00I3: a finite tensor stage is a pair of finitely generated subalgebras. -/
@[stacks 00I3 "finite tensor stage owner"]
structure FGSubalgebraPair (k : Type u) (R : Type v) (S : Type w)
    [CommSemiring k] [CommSemiring R] [CommSemiring S]
    [Algebra k R] [Algebra k S] where
  /-- The finitely generated subalgebra of the left tensor factor. -/
  left : Subalgebra k R
  /-- The finitely generated subalgebra of the right tensor factor. -/
  right : Subalgebra k S
  /-- Finite generation of the left stage. -/
  leftFG : left.FG
  /-- Finite generation of the right stage. -/
  rightFG : right.FG

namespace FGSubalgebraPair

/-- The canonical map from a finite tensor stage to the ambient tensor product. -/
@[stacks 00I3 "finite tensor stage owner"]
def map {k : Type u} {R : Type v} {S : Type w}
    [CommSemiring k] [CommSemiring R] [CommSemiring S]
    [Algebra k R] [Algebra k S]
    (T : FGSubalgebraPair k R S) :
    T.left ⊗[k] T.right →ₐ[k] R ⊗[k] S :=
  Algebra.TensorProduct.map T.left.val T.right.val

/-- The canonical map from a finite tensor stage sends a pure tensor to the
same pure tensor in the ambient tensor product. -/
@[simp, stacks 00I3 "finite tensor stage map computation"]
theorem map_tmul
    {k : Type u} {R : Type v} {S : Type w}
    [CommSemiring k] [CommSemiring R] [CommSemiring S]
    [Algebra k R] [Algebra k S]
    (T : FGSubalgebraPair k R S) (x : T.left) (y : T.right) :
    T.map (x ⊗ₜ[k] y) = (x : R) ⊗ₜ[k] (y : S) := sorry

/-- Tag 00I3: over a field, the canonical map from a finite tensor stage is injective. -/
@[stacks 00I3 "finite tensor stage"]
theorem map_injective
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (T : FGSubalgebraPair k R S) :
    Function.Injective T.map := sorry

/-- Every element of a tensor product over a commutative base already occurs in a finite tensor
stage on both sides. -/
@[stacks 00I3 "finite tensor stage lifting"]
theorem exists_lift
    {k : Type u} {R : Type v} {S : Type w}
    [CommSemiring k] [CommSemiring R] [CommSemiring S]
    [Algebra k R] [Algebra k S]
    (x : R ⊗[k] S) :
    ∃ T : FGSubalgebraPair k R S, ∃ x' : T.left ⊗[k] T.right, T.map x' = x := sorry

/-- Two tensor elements occur simultaneously in one finite tensor stage on both sides. -/
@[stacks 00I3 "finite tensor stage lifting"]
theorem exists_lift_pair
    {k : Type u} {R : Type v} {S : Type w}
    [CommSemiring k] [CommSemiring R] [CommSemiring S]
    [Algebra k R] [Algebra k S]
    (x y : R ⊗[k] S) :
    ∃ T : FGSubalgebraPair k R S, ∃ x' y' : T.left ⊗[k] T.right,
      T.map x' = x ∧ T.map y' = y := sorry

/-- Lemma 10.43.4 (Tag 00I3): nonreducedness of a tensor product over a field is already visible
in a tensor product of finitely generated subalgebras. -/
@[stacks 00I3]
theorem exists_not_isReduced
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (h : ¬ IsReduced (R ⊗[k] S)) :
    ∃ T : FGSubalgebraPair k R S, ¬ IsReduced (T.left ⊗[k] T.right) := sorry

/-- Lemma 10.43.4 (Tag 00I3): nonzero factors with zero product in a tensor product over a field
already occur in a tensor product of finitely generated subalgebras. -/
@[stacks 00I3]
theorem exists_nonzero_mul_eq_zero
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (h : ∃ x y : R ⊗[k] S, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0) :
    ∃ T : FGSubalgebraPair k R S, ∃ x y : T.left ⊗[k] T.right,
      x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 := sorry

/-- Lemma 10.43.4 (Tag 00I3): a nontrivial idempotent in a tensor product over a field already
occurs in a tensor product of finitely generated subalgebras. -/
@[stacks 00I3]
theorem exists_nontrivial_idempotent
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (h : ∃ e : R ⊗[k] S, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1) :
    ∃ T : FGSubalgebraPair k R S, ∃ e : T.left ⊗[k] T.right,
      IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := sorry

end FGSubalgebraPair

end Algebra.TensorProduct
