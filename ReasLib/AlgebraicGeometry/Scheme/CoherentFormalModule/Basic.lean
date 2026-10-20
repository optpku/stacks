/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Coherent formal module systems on schemes

This file defines coherent inverse systems of module sheaves along ideal-sheaf data and bundles
them as a full subcategory.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- An inverse system of coherent modules is a coherent formal module system along `I` when each
affine stage is annihilated by the corresponding power of `I` and each successor map induces the
expected quotient bijection. -/
def IsCoherentFormalModuleSystem {X : Scheme.{u}} (I : X.IdealSheafData) :
    ObjectProperty (SequentialInverseSystem (RingedSpace.Coh X.toRingedSpace)) :=
  fun F ↦
    (∀ n : ℕ, ∀ U : X.affineOpens,
      I.ideal U ^ n •
          (⊤ : Submodule Γ(X, U.1) ((F.obj (op n)).obj.val.obj (op U.1))) = ⊥) ∧
    ∀ n : ℕ, ∀ U : X.affineOpens,
      ∃ hquot :
          I.ideal U ^ n •
              (⊤ : Submodule Γ(X, U.1)
                ((F.obj (op (n + 1))).obj.val.obj (op U.1))) ≤
            (((F.stepMap n).hom.val.app (op U.1)).hom).ker,
        Function.Bijective
          (Submodule.liftQ
            (I.ideal U ^ n •
              (⊤ : Submodule Γ(X, U.1)
                ((F.obj (op (n + 1))).obj.val.obj (op U.1))))
            (((F.stepMap n).hom.val.app (op U.1)).hom)
            hquot)

/-- The full category of coherent formal module systems along ideal-sheaf data `I`. -/
abbrev CoherentFormalModules (X : Scheme.{u}) (I : X.IdealSheafData) :=
  (IsCoherentFormalModuleSystem I).FullSubcategory

/-- An inverse system is a coherent formal module system exactly when its affine stages satisfy
the annihilation and successor-quotient conditions. -/
theorem isCoherentFormalModuleSystem_iff {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : SequentialInverseSystem (RingedSpace.Coh X.toRingedSpace)) :
    IsCoherentFormalModuleSystem I F ↔
      (∀ n : ℕ, ∀ U : X.affineOpens,
        I.ideal U ^ n •
            (⊤ : Submodule Γ(X, U.1) ((F.obj (op n)).obj.val.obj (op U.1))) = ⊥) ∧
      ∀ n : ℕ, ∀ U : X.affineOpens,
        ∃ hquot :
            I.ideal U ^ n •
                (⊤ : Submodule Γ(X, U.1)
                  ((F.obj (op (n + 1))).obj.val.obj (op U.1))) ≤
              (((F.stepMap n).hom.val.app (op U.1)).hom).ker,
          Function.Bijective
            (Submodule.liftQ
              (I.ideal U ^ n •
                (⊤ : Submodule Γ(X, U.1)
                  ((F.obj (op (n + 1))).obj.val.obj (op U.1))))
              (((F.stepMap n).hom.val.app (op U.1)).hom)
              hquot) := sorry

/-- The zero inverse system is a coherent formal module system over a Noetherian scheme. -/
instance isCoherentFormalModuleSystem_containsZero {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : (IsCoherentFormalModuleSystem I).ContainsZero := sorry

/-- Coherent formal module systems over a Noetherian scheme are closed under cokernels. -/
instance isCoherentFormalModuleSystem_isClosedUnderCokernels {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) :
    (IsCoherentFormalModuleSystem I).IsClosedUnderCokernels := sorry

/-- Coherent formal module systems over a Noetherian scheme are closed under finite products. -/
instance isCoherentFormalModuleSystem_isClosedUnderFiniteProducts
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) :
    (IsCoherentFormalModuleSystem I).IsClosedUnderFiniteProducts := sorry

namespace CoherentFormalModules

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The inverse system of module sheaves underlying a coherent formal module. -/
abbrev moduleSystem (F : CoherentFormalModules X I) : SequentialInverseSystem X.Modules :=
  F.obj ⋙ (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι

/-- The inverse limit sheaf underlying a coherent formal module. -/
noncomputable abbrev limitModule (F : CoherentFormalModules X I) : X.Modules :=
  limit (moduleSystem F)

/-- The projection of the inverse limit onto a stage of the formal module. -/
abbrev stageProjection (F : CoherentFormalModules X I) (n : ℕ) :
    limitModule F ⟶ (F.obj.obj (op n)).obj :=
  limit.π (moduleSystem F) (op n)

/-- Taking the inverse limit of the underlying sheaves is functorial. -/
def limitFunctor (I : X.IdealSheafData) : CoherentFormalModules X I ⥤ X.Modules where
  obj := limitModule
  map f := limMap (Functor.whiskerRight f.hom
    (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι)
  map_id := by sorry
  map_comp := by sorry

/-- The limit projections are natural in the coherent formal module. -/
@[reassoc]
theorem limitFunctor_map_stageProjection {F G : CoherentFormalModules X I}
    (f : F ⟶ G) (n : ℕ) :
    (limitFunctor I).map f ≫ stageProjection G n =
      stageProjection F n ≫ (f.hom.app (op n)).hom := sorry

/-- Taking inverse limits sends a zero map of formal modules to zero. -/
@[simp]
theorem limitFunctor_map_zero (F G : CoherentFormalModules X I) :
    (limitFunctor I).map (0 : F ⟶ G) = 0 := sorry

end CoherentFormalModules

end AlgebraicGeometry.Scheme
