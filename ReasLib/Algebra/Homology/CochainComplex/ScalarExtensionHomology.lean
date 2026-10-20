/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Homology maps for change of coefficient algebra -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

noncomputable section

universe u

namespace CochainComplex

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

/-- An algebra homomorphism induces a map between the underlying additive complexes of
scalar extensions, by applying the homomorphism to the coefficient tensor factor. -/
def extendScalarsComplexMap (M : CochainComplex (ModuleCat A) ℤ) (g : B →ₐ[A] C) :
    ((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ⟶
      ((forget₂ (ModuleCat C) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap A C)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) where
  f n := AddCommGrpCat.ofHom
    (TensorProduct.map
      (show (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) →ₗ[A]
          (ModuleCat.restrictScalars (algebraMap A C)).obj (ModuleCat.of C C) from
        { toFun := g
          map_add' := g.map_add
          map_smul' := fun a b ↦ by
            dsimp [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj'] at b ⊢
            change g (algebraMap A B a * b) = algebraMap A C a * g b
            rw [map_mul, g.commutes] })
      (LinearMap.id : M.X n →ₗ[A] M.X n)).toAddMonoidHom
  comm' i j _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul b m => rfl
    | add x y hx hy =>
        exact (AddMonoidHom.map_add _ x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (AddMonoidHom.map_add _ x y).symm)

/-- The coefficient-change map sends a pure tensor `b ⊗ m` to `g(b) ⊗ m`. -/
@[simp]
theorem extendScalarsComplexMap_f_tmul (M : CochainComplex (ModuleCat A) ℤ)
    (g : B →ₐ[A] C) (n : ℤ) (b : B) (m : M.X n) :
    (extendScalarsComplexMap M g).f n (b ⊗ₜ[A, algebraMap A B] m) =
      g b ⊗ₜ[A, algebraMap A C] m := rfl

/-- The map on ordinary homology induced by changing the coefficient algebra is obtained
from the tensor-induced chain map and the exact additive forgetful functors. -/
def extendScalarsHomologyMap (M : CochainComplex (ModuleCat A) ℤ) (g : B →ₐ[A] C)
    (i : ℤ) :
    (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).homology i →
      (((ModuleCat.extendScalars (algebraMap A C)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).homology i :=
  fun x ↦
    (((((ModuleCat.extendScalars (algebraMap A C)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).sc i).mapHomologyIso
          (forget₂ (ModuleCat C) AddCommGrpCat)).hom
      ((HomologicalComplex.homologyMap (extendScalarsComplexMap M g) i)
        ((((((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M).sc i).mapHomologyIso
              (forget₂ (ModuleCat B) AddCommGrpCat)).inv x))

end CochainComplex
