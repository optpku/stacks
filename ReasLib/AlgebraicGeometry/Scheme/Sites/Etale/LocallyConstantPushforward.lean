/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme

/-- A finite étale morphism preserves locally constant sheaves of sets under
the continuous direct image on small étale sites. -/
theorem finiteEtale_pushforward_isLocallyConstant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [HasWeakSheafify X.smallEtaleTopology (Type v)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type v)]
    [HasWeakSheafify Y.smallEtaleTopology (Type v)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type v)]
    (F : Sheaf X.smallEtaleTopology (Type v)) [Sheaf.IsLocallyConstant F] :
    Sheaf.IsLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (Type v) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

/-- A finite étale morphism preserves finite locally constant sheaves of sets
under the continuous direct image on small étale sites. -/
theorem finiteEtale_pushforward_isFiniteLocallyConstant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [HasWeakSheafify X.smallEtaleTopology (Type v)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type v)]
    [HasWeakSheafify Y.smallEtaleTopology (Type v)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type v)]
    (F : Sheaf X.smallEtaleTopology (Type v))
    [Sheaf.IsFiniteLocallyConstant F] :
    Sheaf.IsFiniteLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (Type v) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

/-- A finite étale morphism preserves locally constant sheaves of additive
commutative groups under the continuous direct image on small étale sites. -/
theorem finiteEtale_pushforward_isLocallyConstantAddCommGrp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{w}]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{w}]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    [Sheaf.IsLocallyConstant F] :
    Sheaf.IsLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (AddCommGrpCat.{w}) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

/-- A finite étale morphism preserves finite locally constant sheaves of
additive commutative groups under the continuous direct image on small étale
sites. -/
theorem finiteEtale_pushforward_isFiniteLocallyConstantAddCommGrp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{w}]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{w}]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    [Sheaf.IsFiniteLocallyConstantAddCommGrp F] :
    Sheaf.IsFiniteLocallyConstantAddCommGrp
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (AddCommGrpCat.{w}) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

/-- A finite étale morphism preserves locally constant sheaves of modules
under the continuous direct image on small étale sites. -/
theorem finiteEtale_pushforward_isLocallyConstantModule
    {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] (f : X ⟶ Y)
    [IsFinite f] [Etale f]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
    [Sheaf.IsLocallyConstant F] :
    Sheaf.IsLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

/-- A finite étale morphism preserves finite-type locally constant sheaves of
modules under the continuous direct image on small étale sites. -/
theorem finiteEtale_pushforward_isFiniteTypeLocallyConstantModule
    {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] (f : X ⟶ Y)
    [IsFinite f] [Etale f]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
    [Sheaf.IsFiniteTypeLocallyConstantModule F] :
    Sheaf.IsFiniteTypeLocallyConstantModule
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

end AlgebraicGeometry.Scheme
