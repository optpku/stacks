module

public import ReasLib.Algebra.Module.TensorProduct.Diagonal

/-!
# Mixed-ring endomorphisms of a diagonal tensor product
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

/-- The `A`-action on the diagonal tensor is the restriction of the diagonal
`Λ[G]`-action. -/
instance instIsScalarTower : IsScalarTower A (Λ[G]) (Diagonal A Λ G P M) := sorry

/-- The mixed-ring tensor of endomorphisms `u ⊗ v`, as a `Λ[G]`-endomorphism of
the diagonal tensor `P ⊗[A] M`, sends `p ⊗ m` to `u p ⊗ v m`. -/
def tmulEnd (u : Module.End (A[G]) P) (v : Module.End (Λ[G]) M) :
    Module.End (Λ[G]) (Diagonal A Λ G P M) :=
  let tensorMap := map (u.restrictScalars A) (v.restrictScalars A)
  { toFun := tensorMap
    map_add' := tensorMap.map_add
    map_smul' := sorry }

/-- The mixed-ring tensor of endomorphisms acts on elementary tensors by acting
on each factor. -/
theorem tmulEnd_tmul (u : Module.End (A[G]) P) (v : Module.End (Λ[G]) M) (p : P) (m : M) :
    tmulEnd A Λ G P M u v (tmul A Λ G P M p m) = tmul A Λ G P M (u p) (v m) := sorry

/-- Restricting scalars of `tmulEnd u v` from `Λ[G]` to `A` recovers
`TensorProduct.map` of the `A`-restrictions. -/
theorem tmulEnd_restrictScalars (u : Module.End (A[G]) P) (v : Module.End (Λ[G]) M) :
    (tmulEnd A Λ G P M u v).restrictScalars A =
      map (u.restrictScalars A) (v.restrictScalars A) := sorry

end Diagonal

end TensorProduct
