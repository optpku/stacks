/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
Released under Apache 2.0 license as described in the file LICENSE.
The pointwise-to-represented group-object construction is Mathlib's
`GrpObj.ofRepresentableBy`. The actual torsion-kernel comparison is adapted
from Naganori Yamaguchi's NYLL, 8c1b16d10afaca09e0dc72753c6575e230d31a55;
see Points.lean and the accompanying NOTICE for its original attribution.
-/
module

public import ReasLib.AlgebraicGeometry.GroupScheme.Torsion.Points
public import Mathlib.Algebra.Group.Hom.Basic

/-!
# The group structure of the multiplication kernel

For a commutative group object over an arbitrary scheme, the subgroup of
points killed by `n` is represented by the actual pullback kernel. Transport
the entire group-valued presheaf by Mathlib's representability construction;
this also proves that the comparison preserves the group operations.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.GroupObject

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]

/-- The actual subgroup of the point group annihilated by `n`. -/
abbrev torsionSubgroup (T : Over S) (n : ℕ) : Subgroup (T ⟶ G) :=
  (powMonoidHom (α := T ⟶ G) n).ker

@[simp]
theorem mem_torsionSubgroup (T : Over S) (n : ℕ) (x : T ⟶ G) :
    x ∈ torsionSubgroup G T n ↔ x ^ n = 1 := Iff.rfl

/-- The group-valued torsion functor uses actual precomposition on points. -/
def torsionPointsFunctor (n : ℕ) : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (torsionSubgroup G T.unop n)
  map a := GrpCat.ofHom
    { toFun := restrictTorsionPoints G a.unop n
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' x y := Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    exact Category.id_comp _
  map_comp a b := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- The actual pullback kernel represents the torsion subgroup functor. -/
def torsionPointsRepresentableBy (n : ℕ) :
    (torsionPointsFunctor G n ⋙ CategoryTheory.forget GrpCat).RepresentableBy
      (multiplicationKernel G n) where
  homEquiv {T} := (torsionSubsetEquivSchemeKerPoints G T n).symm
  homEquiv_comp a x := by
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- The canonical group structure on the actual multiplication kernel. -/
@[instance_reducible]
def multiplicationKernelGrpObj (n : ℕ) : GrpObj (multiplicationKernel G n) :=
  GrpObj.ofRepresentableBy (multiplicationKernel G n) (torsionPointsFunctor G n)
    (torsionPointsRepresentableBy G n)

/-- The comparison as an isomorphism of group-valued functors. -/
def kernelPointsIsoTorsion (n : ℕ) :
    letI := multiplicationKernelGrpObj G n
    yonedaGrpObj (multiplicationKernel G n) ≅ torsionPointsFunctor G n :=
  yonedaGrpObjIsoOfRepresentableBy (multiplicationKernel G n)
    (torsionPointsFunctor G n) (torsionPointsRepresentableBy G n)

/-- The original pointwise kernel comparison is a group isomorphism. -/
def torsionSubgroupMulEquivKernelPoints (T : Over S) (n : ℕ) :
    letI := multiplicationKernelGrpObj G n
    torsionSubgroup G T n ≃* (T ⟶ multiplicationKernel G n) :=
  ((kernelPointsIsoTorsion G n).app (op T)).groupIsoToMulEquiv.symm

@[simp]
theorem torsionSubgroupMulEquivKernelPoints_apply (T : Over S) (n : ℕ)
    (x : torsionSubgroup G T n) :
    letI := multiplicationKernelGrpObj G n
    torsionSubgroupMulEquivKernelPoints G T n x =
      torsionSubsetEquivSchemeKerPoints G T n x := rfl

/-- The represented kernel is commutative because each of its point groups is. -/
theorem multiplicationKernel_commutative (n : ℕ) :
    letI := multiplicationKernelGrpObj G n
    IsCommMonObj (multiplicationKernel G n) := by
  letI := multiplicationKernelGrpObj G n
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  let e : (T ⟶ multiplicationKernel G n) ≃* torsionSubgroup G T n :=
    ((kernelPointsIsoTorsion G n).app (op T)).groupIsoToMulEquiv
  refine ⟨⟨fun a b => ?_⟩⟩
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

/-- The canonical commutative group object on the actual multiplication kernel. -/
@[instance_reducible]
def multiplicationKernelCommGrpObj (n : ℕ) : CommGrpObj (multiplicationKernel G n) where
  __ := multiplicationKernelGrpObj G n
  __ := multiplicationKernel_commutative G n

/-- In the commutative case `[n]` is a morphism of group objects. -/
instance multiplyBy_isMonHom (n : ℕ) : IsMonHom (multiplyBy G n) := by
  have h : (((𝟙 (Grp.mk G)) ^ n).hom.hom) = multiplyBy G n := by
    simp [multiplyBy, GrpObj.mulBy, Grp.Hom.hom_pow, Mon.Hom.hom_pow]
  rw [← h]
  infer_instance

end AlgebraicGeometry.Scheme.GroupObject
