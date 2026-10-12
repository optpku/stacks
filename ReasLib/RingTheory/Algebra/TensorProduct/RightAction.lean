/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.ScopedNS

@[expose] public section

/-!
# Right-factor actions on algebra tensor products

Let a monoid `G` act by `S`-algebra endomorphisms on the right factor `B` of
`A ⊗[S] B`.  This file transports that action to the
tensor product.  The choice is deliberately scoped: a tensor product can carry
different actions from its two factors, so consumers select this one with
`open scoped Algebra.TensorProduct.RightAction`.
@stack 0BRG
-/

open scoped TensorProduct

universe u v w x

namespace Algebra.TensorProduct.RightAction

variable {S : Type u} {A : Type v} {B : Type w} {G : Type x}
variable [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra S A] [Algebra S B]
variable [Monoid G] [MulSemiringAction G B] [SMulCommClass G S B]

/-- The tensor-product algebra endomorphism induced by the action on the right factor. -/
@[stacks 0BRG "right-factor tensor algebra endomorphism"]
noncomputable def algHom (g : G) : A ⊗[S] B →ₐ[S] A ⊗[S] B :=
  Algebra.TensorProduct.lTensor (R := S) (S := S) A
    (MulSemiringAction.toAlgHom S B g)

/-- The right-factor tensor endomorphism at the identity is the identity map. -/
@[stacks 0BRG "right-factor tensor action identity"]
theorem ringHom_one :
    (algHom (S := S) (A := A) (B := B) (1 : G)).toRingHom = RingHom.id _ := sorry
-- Proof strategy: apply `Algebra.TensorProduct.ringHom_ext` and evaluate both maps on pure
-- tensors.  Unfold `algHom`, use the computation rule for `Algebra.TensorProduct.lTensor`, and
-- finish with `one_smul` on the right factor.

/-- Right-factor tensor endomorphisms multiply according to the monoid law. -/
@[stacks 0BRG "right-factor tensor action multiplication"]
theorem ringHom_mul (g h : G) :
    (algHom (S := S) (A := A) (B := B) (g * h)).toRingHom =
      (algHom (S := S) (A := A) (B := B) g).toRingHom.comp
        (algHom (S := S) (A := A) (B := B) h).toRingHom := sorry
-- Proof strategy: use `Algebra.TensorProduct.ringHom_ext`; the `lTensor` computation on a pure
-- tensor reduces the equality to `mul_smul g h b` in the right factor.

/-- The monoid homomorphism encoding the action on the right tensor factor. -/
@[stacks 0BRG "right-factor tensor action homomorphism"]
noncomputable def hom : G →* ((A ⊗[S] B) →+* (A ⊗[S] B)) where
  toFun g := (algHom (S := S) (A := A) (B := B) g).toRingHom
  map_one' := ringHom_one (S := S) (A := A) (B := B) (G := G)
  map_mul' := ringHom_mul (S := S) (A := A) (B := B)

/-- The `G`-action on `A ⊗[S] B` transported from the right factor `B`. -/
@[stacks 0BRG "right-factor tensor action", reducible]
noncomputable def action : MulSemiringAction G (A ⊗[S] B) :=
  MulSemiringAction.compHom _ (hom (S := S) (A := A) (B := B) (G := G))

end Algebra.TensorProduct.RightAction

/-! The action is opt-in because actions transported from the two tensor factors
need not agree.  The lower priority preserves an already selected ambient action. -/
scoped[Algebra.TensorProduct.RightAction] attribute [instance 100]
  Algebra.TensorProduct.RightAction.action

namespace Algebra.TensorProduct.RightAction

section

open scoped Algebra.TensorProduct.RightAction

variable {S : Type u} {A : Type v} {B : Type w} {G : Type x}
variable [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra S A] [Algebra S B]
variable [Monoid G] [MulSemiringAction G B] [SMulCommClass G S B]

/-- The right-factor action has its expected value on pure tensors. -/
@[stacks 0BRG "right-factor action on pure tensors"]
theorem smul_tmul (g : G) (a : A) (b : B) :
    g • (a ⊗ₜ[S] b : A ⊗[S] B) = a ⊗ₜ[S] (g • b) := sorry
-- Proof strategy: unfold the scoped `action`, `hom`, and `algHom`; then apply the pure-tensor
-- computation rule for `Algebra.TensorProduct.lTensor`.

/-- The left tensor inclusion is fixed by the right-factor action. -/
@[stacks 0BRG "left tensor inclusion and right-factor action"]
theorem includeLeft_smul (g : G) (a : A) :
    g • ((Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] B) a) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] B) a := sorry
-- Proof strategy: rewrite `includeLeft a` as `a ⊗ₜ[S] 1`, apply `smul_tmul`, and simplify
-- with preservation of `1` by the semiring action.

/-- The right tensor inclusion intertwines the given and transported actions. -/
@[stacks 0BRG "right tensor inclusion and right-factor action"]
theorem includeRight_smul (g : G) (b : B) :
    g • ((Algebra.TensorProduct.includeRight : B →ₐ[S] A ⊗[S] B) b) =
      (Algebra.TensorProduct.includeRight : B →ₐ[S] A ⊗[S] B) (g • b) := sorry
-- Proof strategy: rewrite `includeRight b` as `1 ⊗ₜ[S] b` and apply `smul_tmul`.

/-- Base scalars commute with the transported right-factor action. -/
@[stacks 0BRG "base scalars commute with the right-factor action"]
theorem smulCommClass : SMulCommClass G S (A ⊗[S] B) := sorry
-- Proof strategy: construct `SMulCommClass` and prove its field by tensor induction.  On pure
-- tensors use `smul_tmul`, the tensor scalar relation, and the ambient `SMulCommClass G S B`;
-- the zero and additive cases follow from the two semilinear actions.

end

end Algebra.TensorProduct.RightAction

scoped[Algebra.TensorProduct.RightAction] attribute [instance 100]
  Algebra.TensorProduct.RightAction.smulCommClass

scoped[Algebra.TensorProduct.RightAction] attribute [simp]
  Algebra.TensorProduct.RightAction.smul_tmul
  Algebra.TensorProduct.RightAction.includeLeft_smul
  Algebra.TensorProduct.RightAction.includeRight_smul
