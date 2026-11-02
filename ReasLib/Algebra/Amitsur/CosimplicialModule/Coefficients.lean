/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Amitsur.CosimplicialModule

/-!
# Coefficients for the Amitsur cosimplicial module

An `R`-module extends degreewise to the rings in the Amitsur cosimplicial
algebra. The resulting modules and their scalar-extension maps form a module
over the varying Amitsur rings.
-/

@[expose] public section

noncomputable section

open CategoryTheory ModuleCat Opposite
open scoped ChangeOfRings TensorProduct

universe u

namespace Algebra.Amitsur

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- A vertex map restricts to the canonical map from `R` to its Amitsur stage. -/
theorem vertex_comp_algebraMap (Delta : SimplexCategory)
    (i : Fin (Delta.len + 1)) :
    (vertex R A Delta i).comp (algebraMap R A) =
      algebraMap R ((cosimplicialAlgebra R A).obj Delta) := by
  ext r
  exact (Arrow.cechConerve.ι
    (Arrow.mk (CommAlgCat.ofHom (Algebra.ofId R A))) Delta i).hom.commutes r

/-- The coefficient map along a simplex morphism sends `b ⊗ₜ m` to the
image of `b` tensored with `m`. -/
noncomputable def coefficientsMap (M : ModuleCat.{u} R)
    {Delta Gamma : SimplexCategory} (beta : Delta ⟶ Gamma) :
    (ModuleCat.extendScalars
      (algebraMap R ((cosimplicialAlgebra R A).obj Delta))).obj M ⟶
      (ModuleCat.restrictScalars
        ((cosimplicialCommRing R A).map beta).hom).obj
          ((ModuleCat.extendScalars
            (algebraMap R ((cosimplicialAlgebra R A).obj Gamma))).obj M) :=
  let ringMap := ((cosimplicialCommRing R A).map beta).hom
  let target := (ModuleCat.extendScalars
    (algebraMap R ((cosimplicialAlgebra R A).obj Gamma))).obj M
  let generator : M ⟶
      (ModuleCat.restrictScalars
        (algebraMap R ((cosimplicialAlgebra R A).obj Delta))).obj
          ((ModuleCat.restrictScalars ringMap).obj target) :=
    ModuleCat.ofHom (X := M)
      (Y := (ModuleCat.restrictScalars
        (algebraMap R ((cosimplicialAlgebra R A).obj Delta))).obj
          ((ModuleCat.restrictScalars ringMap).obj target))
    { toFun := fun m ↦
        (1 : (cosimplicialAlgebra R A).obj Gamma) ⊗ₜ[R,
          algebraMap R ((cosimplicialAlgebra R A).obj Gamma)] m
      map_add' := fun _ _ ↦ TensorProduct.tmul_add _ _ _
      map_smul' := by
        intro r m
        change (1 : (cosimplicialAlgebra R A).obj Gamma) ⊗ₜ[R,
            algebraMap R ((cosimplicialAlgebra R A).obj Gamma)] (r • m) =
          (((cosimplicialAlgebra R A).map beta).hom
            (algebraMap R ((cosimplicialAlgebra R A).obj Delta) r) * 1) ⊗ₜ[R,
              algebraMap R ((cosimplicialAlgebra R A).obj Gamma)] m
        rw [AlgHom.commutes]
        letI : Module R ((cosimplicialAlgebra R A).obj Gamma) :=
          Module.compHom _ (algebraMap R ((cosimplicialAlgebra R A).obj Gamma))
        exact (TensorProduct.smul_tmul r
          (1 : (cosimplicialAlgebra R A).obj Gamma) m).symm }
  ((ModuleCat.extendRestrictScalarsAdj
    (algebraMap R ((cosimplicialAlgebra R A).obj Delta))).homEquiv _ _).symm generator

private theorem coefficientsMap_one_tmul (M : ModuleCat.{u} R)
    {Delta Gamma : SimplexCategory} (beta : Delta ⟶ Gamma) (m : M) :
    coefficientsMap R A M beta
        ((1 : (cosimplicialAlgebra R A).obj Delta) ⊗ₜ[R,
          algebraMap R ((cosimplicialAlgebra R A).obj Delta)] m) =
      (1 : (cosimplicialAlgebra R A).obj Gamma) ⊗ₜ[R,
        algebraMap R ((cosimplicialAlgebra R A).obj Gamma)] m := by
  change ((ModuleCat.extendRestrictScalarsAdj
    (algebraMap R ((cosimplicialAlgebra R A).obj Delta))).homEquiv _ _
      (coefficientsMap R A M beta)) m = _
  rw [coefficientsMap, Equiv.apply_symm_apply]
  rfl

/-- The coefficient modules `(A/R)Delta ⊗[R] M`, with their canonical maps,
form a module over the varying Amitsur rings. -/
noncomputable def coefficients (M : ModuleCat.{u} R) :
    CosimplicialModule R A where
  obj X := (ModuleCat.extendScalars
    (algebraMap R ((cosimplicialAlgebra R A).obj (unop (unop X))))).obj M
  map f := coefficientsMap R A M f.unop.unop
  map_id X := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    exact coefficientsMap_one_tmul R A M _ m
  map_comp {X Y Z} f g := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change coefficientsMap R A M (f ≫ g).unop.unop
        ((1 : (cosimplicialAlgebra R A).obj (unop (unop X))) ⊗ₜ[R,
          algebraMap R ((cosimplicialAlgebra R A).obj (unop (unop X)))] m) =
      coefficientsMap R A M g.unop.unop
        (coefficientsMap R A M f.unop.unop
          ((1 : (cosimplicialAlgebra R A).obj (unop (unop X))) ⊗ₜ[R,
            algebraMap R ((cosimplicialAlgebra R A).obj (unop (unop X)))] m))
    rw [coefficientsMap_one_tmul, coefficientsMap_one_tmul]
    exact (coefficientsMap_one_tmul R A M g.unop.unop m).symm

/-- In degree `Delta`, `coefficients` is scalar extension of `M` from `R`
to the corresponding Amitsur ring. -/
theorem coefficients_obj (M : ModuleCat.{u} R) (Delta : SimplexCategory) :
    CosimplicialModule.eval R A (coefficients R A M) Delta =
      (ModuleCat.extendScalars
        (algebraMap R ((cosimplicialAlgebra R A).obj Delta))).obj M := rfl

/-- A coefficient structure map sends `b ⊗ₜ m` to the image of `b`
tensored with `m`. -/
theorem coefficients_map_tmul (M : ModuleCat.{u} R)
    {Delta Gamma : SimplexCategory} (beta : Delta ⟶ Gamma)
    (b : (cosimplicialAlgebra R A).obj Delta) (m : M) :
    coefficientsMap R A M beta
        (b ⊗ₜ[R, algebraMap R ((cosimplicialAlgebra R A).obj Delta)] m) =
      ((cosimplicialAlgebra R A).map beta).hom b ⊗ₜ[R,
        algebraMap R ((cosimplicialAlgebra R A).obj Gamma)] m := by
  have h := (coefficientsMap R A M beta).hom.map_smul b
    ((1 : (cosimplicialAlgebra R A).obj Delta) ⊗ₜ[R,
      algebraMap R ((cosimplicialAlgebra R A).obj Delta)] m)
  rw [coefficientsMap_one_tmul] at h
  change coefficientsMap R A M beta
      ((b * 1) ⊗ₜ[R, algebraMap R ((cosimplicialAlgebra R A).obj Delta)] m) =
    (((cosimplicialAlgebra R A).map beta).hom b * 1) ⊗ₜ[R,
      algebraMap R ((cosimplicialAlgebra R A).obj Gamma)] m at h
  erw [mul_one, mul_one] at h
  exact h

end Algebra.Amitsur
