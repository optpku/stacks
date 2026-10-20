/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AssociatedSheaf
public import stacks_project.Chap58.Theorem_58_6_2_Fiber

/-!
# Finite locally constant sheaves associated to discrete π₁-modules

This leaf owns the sheaf of Λ-modules associated to a finite discrete continuous
π₁-module, as the inverse of the equivalence of Lemma 59.65.1 (3).
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

section sheafOfDiscreteModule

variable {X : Scheme.{u}}
variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The finite-type locally constant étale sheaf associated to a finite discrete
arithmetic fundamental-group module. -/
abbrev sheafOfDiscreteModule [ConnectedSpace X] (ηbar : GeometricPoint X)
    (Mρ : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber ηbar))).FullSubcategory) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  associatedSheaf Λ ηbar Mρ

/-- The associated sheaf is the underlying object of the inverse equivalence applied to `Mρ`. -/
theorem sheafOfDiscreteModule_spec [ConnectedSpace X] (ηbar : GeometricPoint X)
    (Mρ : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber ηbar))).FullSubcategory) :
    sheafOfDiscreteModule Λ ηbar Mρ =
      ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ ηbar).inverse.obj
          Mρ).obj :=
  rfl

/-- The associated sheaf is finite-type locally constant. -/
theorem sheafOfDiscreteModule_isFiniteTypeLocallyConstant [ConnectedSpace X]
    (ηbar : GeometricPoint X)
    (Mρ : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber ηbar))).FullSubcategory) :
    Sheaf.IsFiniteTypeLocallyConstantModule (sheafOfDiscreteModule Λ ηbar Mρ) :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ ηbar).inverse.obj
      Mρ).property

end sheafOfDiscreteModule

section abelianSheafOfModuleSheaf

variable {X : Scheme.{u}}
variable (Λ : Type (u + 1)) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- Forget a sheaf of Λ-modules to a sheaf of abelian groups. -/
def abelianSheafOfModuleSheaf (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F

/-- Unfolding of the forgetful abelian sheaf. -/
theorem abelianSheafOfModuleSheaf_spec (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    abelianSheafOfModuleSheaf Λ F =
      (sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F :=
  rfl

end abelianSheafOfModuleSheaf

end AlgebraicGeometry.Scheme

end
