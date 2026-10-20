/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential.FGModuleCat
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Algebra.Category.ModuleCat.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [CommRing A]

/-- A sequential inverse system of finite `A`-modules is an affine coherent formal module system
along `I` if its stage `n` is annihilated by `I ^ n` and its successor map induces a bijection
from the quotient of stage `n + 1` by `I ^ n` onto stage `n`. -/
def IsAffineCoherentFormalModuleSystem (I : Ideal A) :
    ObjectProperty (SequentialInverseSystem (FGModuleCat A)) :=
  fun F ↦
    (∀ n : ℕ,
      I ^ n • (⊤ : Submodule A (F.stageModule n)) = ⊥) ∧
    ∀ n : ℕ,
      ∃ hquot :
          I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))) ≤ (F.stepLinearMap n).ker,
        Function.Bijective
          (Submodule.liftQ
            (I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))))
            (F.stepLinearMap n)
            hquot)

/-- The full category of affine coherent formal module systems along an ideal `I` of `A`. -/
abbrev AffineCoherentFormalModules (A : Type u) [CommRing A] (I : Ideal A) :=
  (IsAffineCoherentFormalModuleSystem I).FullSubcategory

/-- A finite-module inverse system is an affine coherent formal module system exactly when its
stages are annihilated by the corresponding powers of `I` and its induced successor quotient maps
are bijective. -/
theorem isAffineCoherentFormalModuleSystem_iff {I : Ideal A}
    (F : SequentialInverseSystem (FGModuleCat A)) :
    IsAffineCoherentFormalModuleSystem I F ↔
      (∀ n : ℕ,
        I ^ n • (⊤ : Submodule A (F.stageModule n)) = ⊥) ∧
      ∀ n : ℕ,
        ∃ hquot :
            I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))) ≤ (F.stepLinearMap n).ker,
          Function.Bijective
            (Submodule.liftQ
              (I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))))
              (F.stepLinearMap n)
              hquot) := sorry

namespace AffineCoherentFormalModules

variable [IsNoetherianRing A]

/-- The inverse limit of the finite-module stages of an affine coherent formal module system. -/
noncomputable abbrev limitModule (F : AffineCoherentFormalModules A I) : ModuleCat A :=
  limit (F.obj ⋙ forget₂ (FGModuleCat A) (ModuleCat A))

/-- The finite completed module attached to an affine coherent formal module system. -/
noncomputable def completedModule (I : Ideal A)
    (F : AffineCoherentFormalModules A I) : FGModuleCat (AdicCompletion I A) :=
  ⟨ModuleCat.of (AdicCompletion I A) (AdicCompletion I (limitModule F)), by sorry⟩

/-- The map on completed inverse limits induced by a morphism of affine formal modules. -/
noncomputable def completedModuleMap (I : Ideal A)
    {F G : AffineCoherentFormalModules A I} (f : F ⟶ G) :
    completedModule I F ⟶ completedModule I G :=
  ObjectProperty.homMk <|
    ModuleCat.ofHom
      (AdicCompletion.map I
        (ModuleCat.homEquiv
          (limMap (Functor.whiskerRight f.hom
            (forget₂ (FGModuleCat A) (ModuleCat A))))))

/-- The canonical functor sending an affine formal module system to its completed inverse limit. -/
noncomputable def completionFunctor (I : Ideal A) :
    AffineCoherentFormalModules A I ⥤ FGModuleCat (AdicCompletion I A) where
  obj F := completedModule I F
  map f := completedModuleMap I f
  map_id := by sorry
  map_comp := by sorry

@[simp]
theorem completionFunctor_obj (I : Ideal A)
    (F : AffineCoherentFormalModules A I) :
    (completionFunctor I).obj F = completedModule I F :=
  rfl

@[simp]
theorem completionFunctor_map (I : Ideal A)
    {F G : AffineCoherentFormalModules A I} (f : F ⟶ G) :
    (completionFunctor I).map f = completedModuleMap I f :=
  rfl

/-- The completion functor is an equivalence. -/
instance completionFunctor_isEquivalence (I : Ideal A) :
    (completionFunctor I).IsEquivalence := by
  sorry

/-- The category of affine coherent formal module systems along `I` is equivalent to finite modules
over the `I`-adic completion of `A`. -/
noncomputable def affineCoherentFormalModulesEquiv (I : Ideal A) :
    AffineCoherentFormalModules A I ≌ FGModuleCat (AdicCompletion I A) :=
  (completionFunctor I).asEquivalence

end AffineCoherentFormalModules

end CategoryTheory.SequentialInverseSystem
