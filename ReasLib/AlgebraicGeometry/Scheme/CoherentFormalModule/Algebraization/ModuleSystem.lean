/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Restriction
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.CategoryTheory.InverseSystem.Sequential.FGModuleCat
public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

namespace ModuleSystem

/-- The ideal-power submodule at stage `n + 1` lies in the kernel of the successor map
when stage `n` is annihilated by `I ^ n`. -/
theorem powerSubmodule_le_stepKernel (I : Ideal A)
    (F : SequentialInverseSystem (FGModuleCat A))
    (annihilated : ∀ n : ℕ,
      I ^ n • (⊤ : Submodule A (F.stageModule n)) = ⊥) (n : ℕ) :
    I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))) ≤
      (F.stepLinearMap n).ker := sorry

/-- The successor map induced on the quotient of stage `n + 1` by `I ^ n`. -/
def inducedQuotientStep (S : AffineAlgebraizationSetup A)
    (F : SequentialInverseSystem (FGModuleCat A))
    (annihilated : ∀ n : ℕ,
      S.I ^ n • (⊤ : Submodule A (F.stageModule n)) = ⊥) (n : ℕ) :
    (F.stageModule (n + 1) ⧸
      (S.I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))))) →ₗ[A]
        F.stageModule n :=
  Submodule.liftQ
    (S.I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))))
    (F.stepLinearMap n) (powerSubmodule_le_stepKernel S.I F annihilated n)

end ModuleSystem

/-- A finite-module inverse system satisfying the annihilation and power-torsion
conditions of the affine algebraization setup. -/
structure ModuleSystem (S : AffineAlgebraizationSetup A) where
  /-- The inverse system of finite `A`-modules. -/
  system : SequentialInverseSystem (FGModuleCat A)
  /-- Stage `n` is annihilated by `I ^ n`. -/
  annihilated : ∀ n : ℕ,
    S.I ^ n • (⊤ : Submodule A (system.stageModule n)) = ⊥
  /-- The kernel of the induced quotient transition is `a`-power torsion. -/
  transitionKernelTorsion : ∀ n : ℕ,
    Module.IsIdealPowerTorsion S.a
      (ModuleSystem.inducedQuotientStep S system annihilated n).ker
  /-- The cokernel of the induced quotient transition is `a`-power torsion. -/
  transitionCokernelTorsion : ∀ n : ℕ,
    Module.IsIdealPowerTorsion S.a
      (system.stageModule n ⧸
        (ModuleSystem.inducedQuotientStep S system annihilated n).range)

namespace ModuleSystem

/-- Construct a module system from an inverse system satisfying the three source conditions. -/
def of (S : AffineAlgebraizationSetup A)
    (system : SequentialInverseSystem (FGModuleCat A))
    (annihilated : ∀ n : ℕ,
      S.I ^ n • (⊤ : Submodule A (system.stageModule n)) = ⊥)
    (transitionKernelTorsion : ∀ n : ℕ,
      Module.IsIdealPowerTorsion S.a
        (inducedQuotientStep S system annihilated n).ker)
    (transitionCokernelTorsion : ∀ n : ℕ,
      Module.IsIdealPowerTorsion S.a
        (system.stageModule n ⧸ (inducedQuotientStep S system annihilated n).range)) :
    ModuleSystem S where
  system := system
  annihilated := annihilated
  transitionKernelTorsion := transitionKernelTorsion
  transitionCokernelTorsion := transitionCokernelTorsion

/-- The quotient transition attached to a module system. -/
def quotientStep (S : AffineAlgebraizationSetup A) (M : ModuleSystem S) (n : ℕ) :
    (M.system.stageModule (n + 1) ⧸
      (S.I ^ n • (⊤ : Submodule A (M.system.stageModule (n + 1))))) →ₗ[A]
        M.system.stageModule n :=
  inducedQuotientStep S M.system M.annihilated n

/-- The class of an element in the source of the induced quotient transition. -/
def quotientClass (S : AffineAlgebraizationSetup A) (M : ModuleSystem S)
    (n : ℕ) (x : M.system.stageModule (n + 1)) :
    M.system.stageModule (n + 1) ⧸
      (S.I ^ n • (⊤ : Submodule A (M.system.stageModule (n + 1)))) :=
  Submodule.mkQ
    (S.I ^ n • (⊤ : Submodule A (M.system.stageModule (n + 1)))) x

/-- The induced quotient transition sends the class of `x` to the successor transition of `x`. -/
theorem quotientStep_mk (S : AffineAlgebraizationSetup A) (M : ModuleSystem S)
    (n : ℕ) (x : M.system.stageModule (n + 1)) :
    M.quotientStep S n (M.quotientClass S n x) =
      M.system.stepLinearMap n x := sorry

/-- The defining conditions of a module system, exposed together in source order. -/
theorem spec (S : AffineAlgebraizationSetup A) (M : ModuleSystem S) :
    (∀ n : ℕ, S.I ^ n • (⊤ : Submodule A (M.system.stageModule n)) = ⊥) ∧
    (∀ n : ℕ, Module.IsIdealPowerTorsion S.a (M.quotientStep S n).ker) ∧
    ∀ n : ℕ, Module.IsIdealPowerTorsion S.a
      (M.system.stageModule n ⧸ (M.quotientStep S n).range) := sorry

end ModuleSystem

/-- The associated module sheaf on `Spec A` of a finite `A`-module. -/
def tildeObject (M : FGModuleCat A) :=
  (tilde.functor (CommRingCat.of A)).obj M.obj

/-- The associated coherent module sheaf on `Spec A` of a finite `A`-module is coherent. -/
theorem tilde_isCoherent (M : FGModuleCat A) :
    (tildeObject M).IsCoherent := sorry

/-- The functor sending a finite `A`-module to its associated coherent module on `Spec A`. -/
def coherentTildeFunctor :
    FGModuleCat A ⥤ RingedSpace.Coh (Spec (CommRingCat.of A)).toRingedSpace :=
  (SheafOfModules.isCoherent
      (Spec (CommRingCat.of A)).toRingedSpace.ringCatSheaf).lift
    (forget₂ (FGModuleCat A) (ModuleCat A) ⋙
      tilde.functor (CommRingCat.of A))
    tilde_isCoherent

/-- The associated morphism of module sheaves on `Spec A`. -/
def tildeMap {M N : FGModuleCat A} (f : M ⟶ N) :
    tildeObject M ⟶ tildeObject N :=
  (tilde.functor (CommRingCat.of A)).map f.hom

/-- Associate a coherent module on `U` to a finite `A`-module by tilde and restriction. -/
def restrictedTildeFunctor (S : AffineAlgebraizationSetup A) :
    FGModuleCat A ⥤ RingedSpace.Coh S.U.toScheme.toRingedSpace :=
  coherentTildeFunctor ⋙ Scheme.Modules.coherentRestrictFunctor S.U.ι

/-- The object part of `restrictedTildeFunctor` is tilde followed by restriction to `U`. -/
theorem restrictedTildeFunctor_obj (S : AffineAlgebraizationSetup A)
    (M : FGModuleCat A) :
    ((restrictedTildeFunctor S).obj M).obj =
      (Scheme.Modules.restrictFunctor S.U.ι).obj (tildeObject M) := sorry

/-- The map part of `restrictedTildeFunctor` is the restricted tilde map. -/
theorem restrictedTildeFunctor_map (S : AffineAlgebraizationSetup A)
    {M N : FGModuleCat A} (f : M ⟶ N) :
    ((restrictedTildeFunctor S).map f).hom =
      (Scheme.Modules.restrictFunctor S.U.ι).map (tildeMap f) := sorry

namespace ModuleSystem

/-- The inverse system of restricted associated sheaves `(M̃_n|_U)`. -/
def restrictedTilde (S : AffineAlgebraizationSetup A) (M : ModuleSystem S) :
    SequentialInverseSystem (RingedSpace.Coh S.U.toScheme.toRingedSpace) :=
  M.system ⋙ restrictedTildeFunctor S

/-- Stage `n` of the restricted tilde system is the restriction of `M̃_n` to `U`. -/
theorem restrictedTilde_obj (S : AffineAlgebraizationSetup A)
    (M : ModuleSystem S) (n : ℕ) :
    ((M.restrictedTilde S).obj (op n)).obj =
      (Scheme.Modules.restrictFunctor S.U.ι).obj
        (tildeObject (M.system.obj (op n))) := sorry

/-- The restricted tilde system of a module system is a coherent formal module system. -/
theorem restrictedTilde_mem (S : AffineAlgebraizationSetup A) (M : ModuleSystem S) :
    Scheme.IsCoherentFormalModuleSystem
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)
      (M.restrictedTilde S) := sorry

/-- The coherent formal module on `U` realized by a module system. -/
def toFormalModule (S : AffineAlgebraizationSetup A) (M : ModuleSystem S) :
    Scheme.CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) :=
  ⟨M.restrictedTilde S, M.restrictedTilde_mem S⟩

/-- The underlying inverse system of the realized formal module is the restricted tilde system. -/
theorem toFormalModule_obj (S : AffineAlgebraizationSetup A) (M : ModuleSystem S) :
    (M.toFormalModule S).obj = M.restrictedTilde S := sorry

/-- Every coherent formal module on `U` is isomorphic to one realized by a finite-module inverse system. -/
theorem exists_model (S : AffineAlgebraizationSetup A)
    (F : Scheme.CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    ∃ M : ModuleSystem S, Nonempty (M.toFormalModule S ≅ F) := sorry

end ModuleSystem

end AlgebraicGeometry.AffineAlgebraizationSetup
