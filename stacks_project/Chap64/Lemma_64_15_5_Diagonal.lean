/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.TensorProduct.Diagonal

/- A typed compatibility check for the reusable diagonal tensor owner. -/

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

/- The shared owner provides the additive tensor equivalence on the diagonal synonym. -/
#check (TensorProduct.Diagonal.addEquiv A Λ G P M :
  TensorProduct.Diagonal A Λ G P M ≃+ P ⊗[A] M)

end TensorProduct
