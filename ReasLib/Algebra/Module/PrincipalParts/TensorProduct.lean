/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IsTensorProduct
public import ReasLib.Algebra.Module.PrincipalParts.BaseChange
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal Parts and Tensor-Product Base Change

This leaf specializes `PrincipalParts.BaseChange.map` to the canonical
pushout `S ⊗[R] T`.  It owns the base-change predicate and its bijectivity
consequence, while the underlying map remains the general map from the
`PrincipalParts.BaseChange` leaf.

@stack 0H8Z
-/

@[expose] public section

universe u

noncomputable section

open scoped TensorProduct Algebra.TensorProduct.Right

namespace PrincipalParts.BaseChange.TensorProduct

section

variable {R S T M : Type u}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- Lemma 10.133.8 (Tag 0H8Z): for the tensor-product pushout `S ⊗[R] T`, the canonical
principal-parts comparison realizes the target as the base change of the source. -/
@[stacks 0H8Z]
theorem isBaseChange (k : ℕ) :
    IsBaseChange (S ⊗[R] T)
      (BaseChange.map (A := R) (B := S) (A' := T) (B' := S ⊗[R] T) (M := M)
        (M' := (S ⊗[R] T) ⊗[S] M) k
        (TensorProduct.mk S (S ⊗[R] T) M 1)) := sorry

/-- Lemma 10.133.8: lifting the canonical principal-parts comparison along the tensor-product
base change is bijective. -/
@[stacks 0H8Z]
theorem lift_bijective (k : ℕ) :
    Function.Bijective
      (((BaseChange.map (A := R) (B := S) (A' := T) (B' := S ⊗[R] T) (M := M)
          (M' := (S ⊗[R] T) ⊗[S] M) k
          (TensorProduct.mk S (S ⊗[R] T) M 1)).liftBaseChange (S ⊗[R] T)) :
        (S ⊗[R] T) ⊗[S] PrincipalParts.module R S M k →ₗ[S ⊗[R] T]
          PrincipalParts.module T (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] M) k) := sorry

end

end PrincipalParts.BaseChange.TensorProduct

end
