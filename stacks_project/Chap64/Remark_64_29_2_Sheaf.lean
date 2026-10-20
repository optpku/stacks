/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AssociatedSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [ConnectedSpace X]
variable (xbar : GeometricPoint X)
variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The locally constant sheaf associated to a finite discrete fundamental-group module. -/
abbrev sheafOfPi1Module
    (M : (finiteTypeDiscreteModule Λ
      (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  associatedSheaf Λ xbar M

/-- The sheaf associated to a finite discrete fundamental-group module is locally constant
of finite type. -/
instance sheafOfPi1Module_isFiniteTypeLocallyConstant
    (M : (finiteTypeDiscreteModule Λ
      (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    Sheaf.IsFiniteTypeLocallyConstantModule (sheafOfPi1Module xbar Λ M) :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).inverse.obj
    M).property

end AlgebraicGeometry.Scheme
