module

public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.Subcategory
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Coherent formal modules on schemes

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

/-- Coherent formal module systems over a Noetherian scheme are closed under kernels. -/
instance isCoherentFormalModuleSystem_isClosedUnderKernels {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) :
    (IsCoherentFormalModuleSystem I).IsClosedUnderKernels := sorry

/-- Coherent formal module systems over a Noetherian scheme are closed under cokernels. -/
instance isCoherentFormalModuleSystem_isClosedUnderCokernels {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) :
    (IsCoherentFormalModuleSystem I).IsClosedUnderCokernels := sorry

/-- Coherent formal module systems over a Noetherian scheme are closed under finite products. -/
instance isCoherentFormalModuleSystem_isClosedUnderFiniteProducts
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) :
    (IsCoherentFormalModuleSystem I).IsClosedUnderFiniteProducts := sorry

/-- Coherent formal modules over a Noetherian scheme form an abelian category. -/
noncomputable opaque coherentFormalModules_abelian {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : Abelian (CoherentFormalModules X I) :=
  CategoryTheory.ObjectProperty.instAbelianFullSubcategoryOfContainsZeroOfIsClosedUnderKernelsOfIsClosedUnderCokernelsOfIsClosedUnderFiniteProducts
    (IsCoherentFormalModuleSystem I)

attribute [instance] coherentFormalModules_abelian

end AlgebraicGeometry.Scheme
