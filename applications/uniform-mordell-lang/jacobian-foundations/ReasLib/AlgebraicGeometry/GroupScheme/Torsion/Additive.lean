/-
Copyright (c) 2026 ReasLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ReasLib.AlgebraicGeometry.GroupScheme.Torsion.Quotient

/-! # The additive torsion comparison

This is the additive view of the existing pointwise equivalence, with the
canonical represented group structure stated explicitly. It reuses both
inverse laws and introduces no independent carrier or group law.
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.GroupObject

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G] (T : Over S)

/-- The actual integer-annihilator subgroup as the additive points of the scheme kernel. -/
def torsionByAddEquivSchemeKerPoints (n : ℕ) :
    letI := multiplicationKernelGrpObj G n
    AddSubgroup.torsionBy (AdditivePoints G T) (n : ℤ) ≃+
      Additive (T ⟶ multiplicationKernel G n) := by
  letI := multiplicationKernelGrpObj G n
  let e := torsionByEquivSchemeKerPoints G T n
  refine
    { toFun := fun x => Additive.ofMul (e x)
      invFun := fun z => e.symm z.toMul
      left_inv := fun x => e.symm_apply_apply x
      right_inv := fun z => congrArg Additive.ofMul (e.apply_symm_apply z.toMul)
      map_add' := ?_ }
  intro x y
  exact congrArg Additive.ofMul
    ((torsionSubgroupMulEquivKernelPoints G T n).map_mul
      (additiveTorsionEquiv G T n x) (additiveTorsionEquiv G T n y))

@[simp]
theorem torsionByAddEquivSchemeKerPoints_apply (n : ℕ)
    (x : AddSubgroup.torsionBy (AdditivePoints G T) (n : ℤ)) :
    letI := multiplicationKernelGrpObj G n
    torsionByAddEquivSchemeKerPoints G T n x =
      Additive.ofMul (torsionByEquivSchemeKerPoints G T n x) := rfl

@[simp]
theorem torsionByAddEquivSchemeKerPoints_comp_inclusion (n : ℕ)
    (x : AddSubgroup.torsionBy (AdditivePoints G T) (n : ℤ)) :
    letI := multiplicationKernelGrpObj G n
    (torsionByAddEquivSchemeKerPoints G T n x).toMul ≫ kernelInclusion G n =
      x.1.toMul :=
  torsionByEquivSchemeKerPoints_comp_inclusion G T n x

end AlgebraicGeometry.Scheme.GroupObject
