/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
      algebraMap R ((cosimplicialAlgebra R A).obj Delta) := sorry

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
      map_add' := sorry
      map_smul' := sorry }
  ((ModuleCat.extendRestrictScalarsAdj
    (algebraMap R ((cosimplicialAlgebra R A).obj Delta))).homEquiv _ _).symm generator

/-- The coefficient modules `(A/R)Delta ⊗[R] M`, with their canonical maps,
form a module over the varying Amitsur rings. -/
noncomputable def coefficients (M : ModuleCat.{u} R) :
    CosimplicialModule R A where
  obj X := (ModuleCat.extendScalars
    (algebraMap R ((cosimplicialAlgebra R A).obj (unop (unop X))))).obj M
  map f := coefficientsMap R A M f.unop.unop
  map_id := sorry
  map_comp := sorry

/-- In degree `Delta`, `coefficients` is scalar extension of `M` from `R`
to the corresponding Amitsur ring. -/
theorem coefficients_obj (M : ModuleCat.{u} R) (Delta : SimplexCategory) :
    CosimplicialModule.eval R A (coefficients R A M) Delta =
      (ModuleCat.extendScalars
        (algebraMap R ((cosimplicialAlgebra R A).obj Delta))).obj M := sorry

/-- A coefficient structure map sends `b ⊗ₜ m` to the image of `b`
tensored with `m`. -/
theorem coefficients_map_tmul (M : ModuleCat.{u} R)
    {Delta Gamma : SimplexCategory} (beta : Delta ⟶ Gamma)
    (b : (cosimplicialAlgebra R A).obj Delta) (m : M) :
    coefficientsMap R A M beta
        (b ⊗ₜ[R, algebraMap R ((cosimplicialAlgebra R A).obj Delta)] m) =
      ((cosimplicialAlgebra R A).map beta).hom b ⊗ₜ[R,
        algebraMap R ((cosimplicialAlgebra R A).obj Gamma)] m := sorry

end Algebra.Amitsur
