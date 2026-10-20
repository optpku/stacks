/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.TensorProduct.Diagonal.End

/-!
# Mixed-ring tensor of endomorphisms on the diagonal tensor

The shared diagonal endomorphism API provides the `Λ[G]`-endomorphism `u ⊗ v` of the tensor
`P ⊗[A] M`, obtained from `TensorProduct.map` of the `A`-restrictions of
`u : Module.End (A[G]) P` and `v : Module.End (Λ[G]) M`.
-/

@[expose] public section

noncomputable section

universe u v w p m

open scoped MonoidAlgebra TensorProduct

namespace TensorProduct

variable (A : Type u) (Λ : Type v) (G : Type w) (P : Type p) (M : Type m)
variable [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
variable [AddCommGroup P] [Module A P]
variable [AddCommGroup M] [Module A M]
variable [Module Λ M] [IsScalarTower A Λ M]
variable [Module (A[G]) P] [IsScalarTower A (A[G]) P]
variable [Module (Λ[G]) M] [IsScalarTower Λ (Λ[G]) M]

namespace Diagonal

/- The `A`-action on the diagonal tensor is the restriction of the diagonal
`Λ[G]`-action. -/
#check (TensorProduct.Diagonal.instIsScalarTower A Λ G P M :
  IsScalarTower A (Λ[G]) (Diagonal A Λ G P M))

/- The mixed-ring tensor of endomorphisms `u ⊗ v`, as a `Λ[G]`-endomorphism of
the diagonal tensor `P ⊗[A] M`. On elementary tensors this is
`p ⊗ m ↦ u p ⊗ v m`. -/
#check (TensorProduct.Diagonal.tmulEnd A Λ G P M :
  Module.End (A[G]) P → Module.End (Λ[G]) M → Module.End (Λ[G]) (Diagonal A Λ G P M))

/- The mixed-ring tensor of endomorphisms acts on elementary tensors by acting
on each factor. -/
#check (TensorProduct.Diagonal.tmulEnd_tmul A Λ G P M :
  ∀ (u : Module.End (A[G]) P) (v : Module.End (Λ[G]) M) (p : P) (m : M),
    tmulEnd A Λ G P M u v (tmul A Λ G P M p m) = tmul A Λ G P M (u p) (v m))

/- Restricting scalars of `tmulEnd u v` from `Λ[G]` to `A` recovers
`TensorProduct.map` of the `A`-restrictions. -/
#check (TensorProduct.Diagonal.tmulEnd_restrictScalars A Λ G P M :
  ∀ (u : Module.End (A[G]) P) (v : Module.End (Λ[G]) M),
    (tmulEnd A Λ G P M u v).restrictScalars A =
      map (u.restrictScalars A) (v.restrictScalars A))

end Diagonal

end TensorProduct
