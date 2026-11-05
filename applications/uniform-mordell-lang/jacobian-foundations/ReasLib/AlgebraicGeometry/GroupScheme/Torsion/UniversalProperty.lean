/-
Copyright (c) 2026 ReasLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This file exposes the pointwise universal property of the multiplication
kernel.  The underlying fibre and its point comparison remain owned by
`Torsion.Points`; this module only names the lift, its equations, and the
small consequences needed by consumers.
-/
module

public import ReasLib.AlgebraicGeometry.GroupScheme.Torsion.Group
public import ReasLib.CategoryTheory.Monoidal.Cartesian.Pointwise

/-!
# Universal property of a multiplication kernel

The fibre of `[n]` at the identity is a kernel in the functor-of-points
sense.  This statement is valid for every base scheme and every group object;
commutativity is used only for the group-object operations on the fibre.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.GroupObject

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- The inclusion of the multiplication kernel is monic, without a
commutativity or geometric hypothesis. -/
instance kernelInclusion_mono (n : ℕ) : Mono (kernelInclusion G n) where
  right_cancellation {T} a b h := by
    apply (torsionSubsetEquivSchemeKerPoints G T n).symm.injective
    exact Subtype.ext h

/-- A point whose image under `[n]` is the identity lifts to the fibre. -/
def kernelLift {T : Over S} (n : ℕ) (x : T ⟶ G)
    (hx : x ≫ multiplyBy G n = 1) : T ⟶ multiplicationKernel G n :=
  torsionSubsetEquivSchemeKerPoints G T n
    ⟨x, (comp_multiplyBy G x n).symm.trans hx⟩

@[simp]
theorem kernelLift_comp_inclusion {T : Over S} (n : ℕ) (x : T ⟶ G)
    (hx : x ≫ multiplyBy G n = 1) :
    kernelLift G n x hx ≫ kernelInclusion G n = x := by
  exact torsionSubsetEquivSchemeKerPoints_comp_inclusion G T n _

@[simp]
theorem kernelLift_comp_fst {T : Over S} (n : ℕ) (x : T ⟶ G)
    (hx : x ≫ multiplyBy G n = 1) :
    (kernelLift G n x hx).left ≫
        pullback.fst (multiplyBy G n).left (identitySection G).left =
      x.left := by
  exact torsionSubsetEquivSchemeKerPoints_comp_fst G T n _

/-- The lift is unique among morphisms with the prescribed image in `G`. -/
theorem kernelLift_unique {T : Over S} (n : ℕ) (x : T ⟶ G)
    (hx : x ≫ multiplyBy G n = 1) (u : T ⟶ multiplicationKernel G n)
    (hu : u ≫ kernelInclusion G n = x) :
    u = kernelLift G n x hx := by
  apply (cancel_mono (kernelInclusion G n)).1
  rw [hu, kernelLift_comp_inclusion]

/-- A form of uniqueness that does not mention a chosen point. -/
theorem kernelLift_unique' {T : Over S} (n : ℕ)
    (u v : T ⟶ multiplicationKernel G n)
    (h : u ≫ kernelInclusion G n = v ≫ kernelInclusion G n) : u = v := by
  exact (cancel_mono (kernelInclusion G n)).1 h

/-- The kernel equation in `G`: every point of the fibre is killed by `[n]`. -/
theorem inclusion_comp_multiplyBy (n : ℕ) :
    kernelInclusion G n ≫ multiplyBy G n = 1 := by
  rw [comp_multiplyBy]
  have h := ((torsionSubsetEquivSchemeKerPoints G (multiplicationKernel G n) n).symm
    (𝟙 (multiplicationKernel G n))).2
  change ((𝟙 (multiplicationKernel G n)) ≫ kernelInclusion G n) ^ n = 1 at h
  simpa only [Category.id_comp] using h

/-- Naturality of the canonical lift in the test scheme. -/
theorem kernelLift_natural {T T' : Over S} (a : T' ⟶ T) (n : ℕ)
    (x : T ⟶ G) (hx : x ≫ multiplyBy G n = 1) :
    a ≫ kernelLift G n x hx =
      kernelLift G n (a ≫ x) (by
        rw [Category.assoc, hx]
        exact MonObj.comp_one a) := by
  apply (cancel_mono (kernelInclusion G n)).1
  simp [Category.assoc]

/-- At `n = 0` the fibre is canonically the original group object. -/
def zeroKernelIso : multiplicationKernel G 0 ≅ G where
  hom := kernelInclusion G 0
  inv := kernelLift G 0 (𝟙 G) (by simp [multiplyBy])
  hom_inv_id := by
    apply (cancel_mono (kernelInclusion G 0)).1
    simp [Category.assoc]
  inv_hom_id := by
    simp

@[simp]
theorem zeroKernelIso_hom : (zeroKernelIso G).hom = kernelInclusion G 0 := rfl

@[simp]
theorem zeroKernelIso_inv_comp_inclusion :
    (zeroKernelIso G).inv ≫ kernelInclusion G 0 = 𝟙 G := by
  simp [zeroKernelIso]

/-- The point set of the `n = 1` fibre is subsingleton, with no commutativity
assumption. -/
theorem kernelPoints_subsingleton_one (T : Over S) :
    Subsingleton (T ⟶ multiplicationKernel G 1) := by
  let e := torsionSubsetEquivSchemeKerPoints G T 1
  constructor
  intro u v
  apply (cancel_mono (kernelInclusion G 1)).1
  have hu : (u ≫ kernelInclusion G 1) ^ (1 : ℕ) = 1 := (e.symm u).2
  have hv : (v ≫ kernelInclusion G 1) ^ (1 : ℕ) = 1 := (e.symm v).2
  simpa only [pow_one] using hu.trans hv.symm

variable [IsCommMonObj G]

/-- The inclusion preserves multiplication on every group of points. -/
theorem kernelInclusion_point_mul (T : Over S) (n : ℕ) :
    letI := multiplicationKernelGrpObj G n
    ∀ x y : T ⟶ multiplicationKernel G n,
      (x * y) ≫ kernelInclusion G n =
        (x ≫ kernelInclusion G n) * (y ≫ kernelInclusion G n) := by
  letI := multiplicationKernelGrpObj G n
  intro x y
  exact congrArg Subtype.val
    ((torsionSubgroupMulEquivKernelPoints G T n).symm.map_mul x y)

/-- The inclusion preserves the identity point. -/
theorem kernelInclusion_point_one (T : Over S) (n : ℕ) :
    letI := multiplicationKernelGrpObj G n
    (1 : T ⟶ multiplicationKernel G n) ≫ kernelInclusion G n = 1 := by
  letI := multiplicationKernelGrpObj G n
  exact congrArg Subtype.val
    (torsionSubgroupMulEquivKernelPoints G T n).symm.map_one

/-- The canonical inclusion is a morphism of group objects. -/
instance kernelInclusion_isMonHom (n : ℕ) :
    letI := multiplicationKernelGrpObj G n
    IsMonHom (kernelInclusion G n) := by
  letI := multiplicationKernelGrpObj G n
  exact IsMonHom.of_pointwise (kernelInclusion G n)
    (fun T => kernelInclusion_point_one G T n)
    (fun T x y => kernelInclusion_point_mul G T n x y)

end AlgebraicGeometry.Scheme.GroupObject
