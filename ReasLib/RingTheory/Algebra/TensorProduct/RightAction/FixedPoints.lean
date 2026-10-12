/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Invariant.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAction

@[expose] public section

/-!
# Fixed points of a right-factor tensor action

This leaf packages the fixed subalgebra of the scoped right-factor action on
`A ⊗[S] B` and the canonical map into it from the left factor.  These objects
only need a monoid action; hypotheses identifying the fixed points of `B` with
the base `S` belong to invariant-theory companion files.

@stack 0BRG
-/

open scoped TensorProduct Algebra.TensorProduct.RightAction

universe u v w x

namespace Algebra.TensorProduct.RightAction

variable {S : Type u} {A : Type v} {B : Type w} {G : Type x}
variable [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra S A] [Algebra S B]
variable [Monoid G] [MulSemiringAction G B] [SMulCommClass G S B]

/-- The fixed subalgebra of `A ⊗[S] B` for the right-factor action. -/
@[stacks 0BRG "fixed subalgebra of a right-factor tensor action"]
noncomputable def fixedSubalgebra : Subalgebra S (A ⊗[S] B) :=
  FixedPoints.subalgebra S (A ⊗[S] B) G

/-- The left tensor inclusion lands in the fixed subalgebra. -/
@[stacks 0BRG "left tensor inclusion lands in right-action fixed points"]
theorem includeLeft_mem_fixed (a : A) :
    (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] B) a ∈
      fixedSubalgebra (S := S) (A := A) (B := B) (G := G) := sorry
-- Proof strategy: unfold membership in `FixedPoints.subalgebra`, introduce `g : G`, and apply
-- `RightAction.includeLeft_smul`.

/-- The canonical algebra map from the left factor to the fixed subalgebra. -/
@[stacks 0BRG "canonical map to right-action fixed points"]
noncomputable def toFixed :
    A →ₐ[S] fixedSubalgebra (S := S) (A := A) (B := B) (G := G) :=
  (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] B).codRestrict
    (fixedSubalgebra (S := S) (A := A) (B := B) (G := G))
    (includeLeft_mem_fixed (S := S) (A := A) (B := B) (G := G))

/-- Forgetting the fixed-point codomain recovers the left tensor inclusion pointwise. -/
@[simp, stacks 0BRG "canonical fixed-point map value"]
theorem coe_toFixed (a : A) :
    (toFixed (S := S) (A := A) (B := B) (G := G) a : A ⊗[S] B) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] B) a := sorry
-- Proof strategy: unfold `toFixed`; this is the coercion rule for `AlgHom.codRestrict`.

/-- The fixed-point map followed by subtype inclusion is the left tensor inclusion. -/
@[simp, stacks 0BRG "canonical fixed-point map composition"]
theorem val_comp_toFixed :
    (fixedSubalgebra (S := S) (A := A) (B := B) (G := G)).val.comp
        (toFixed (S := S) (A := A) (B := B) (G := G)) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] B) := sorry
-- Proof strategy: apply `AlgHom.ext` and discharge the pointwise equality with `coe_toFixed`.

/-- Codomain restriction to fixed points does not change the kernel. -/
@[stacks 0BRG "kernel of the canonical fixed-point map"]
theorem ker_toFixed :
    RingHom.ker (toFixed (S := S) (A := A) (B := B) (G := G)).toRingHom =
      RingHom.ker
        (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] B).toRingHom := sorry
-- Proof strategy: ext `a`; rewrite both ideal memberships with `RingHom.mem_ker`, coerce equality
-- in the fixed subalgebra through `Subtype.ext_iff`, and finish with `coe_toFixed`.

/- The fixed subalgebra and codomain-restricted map have explicit data.  Their
`sorryAx` dependencies are confined to the selected action laws and membership proofs. -/

end Algebra.TensorProduct.RightAction
