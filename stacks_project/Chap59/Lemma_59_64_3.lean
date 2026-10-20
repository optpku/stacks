/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocallyConstantPushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

/- Lemma 59.64.3 (1): finite étale pushforward preserves locally constant
set-valued sheaves on the small étale site. -/
@[stacks 095B]
#check
  (AlgebraicGeometry.Scheme.finiteEtale_pushforward_isLocallyConstant :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
      [HasWeakSheafify X.smallEtaleTopology (Type v)]
      [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type v)]
      [HasWeakSheafify Y.smallEtaleTopology (Type v)]
      [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type v)]
      (F : Sheaf X.smallEtaleTopology (Type v)) [Sheaf.IsLocallyConstant F],
    Sheaf.IsLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (Type v) Y.smallEtaleTopology X.smallEtaleTopology).obj F))

/- Lemma 59.64.3 (2): finite étale pushforward preserves finite locally
constant set-valued sheaves on the small étale site. -/
@[stacks 095B]
#check
  (AlgebraicGeometry.Scheme.finiteEtale_pushforward_isFiniteLocallyConstant :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
      [HasWeakSheafify X.smallEtaleTopology (Type v)]
      [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type v)]
      [HasWeakSheafify Y.smallEtaleTopology (Type v)]
      [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type v)]
      (F : Sheaf X.smallEtaleTopology (Type v))
      [Sheaf.IsFiniteLocallyConstant F],
    Sheaf.IsFiniteLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (Type v) Y.smallEtaleTopology X.smallEtaleTopology).obj F))

/- Lemma 59.64.3 (3): finite étale pushforward preserves locally constant
abelian-group-valued sheaves on the small étale site. -/
@[stacks 095B]
#check
  (AlgebraicGeometry.Scheme.finiteEtale_pushforward_isLocallyConstantAddCommGrp :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
      [∀ U : X.Etale,
        HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{w}]
      [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
      [∀ U : Y.Etale,
        HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{w}]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
      [Sheaf.IsLocallyConstant F],
    Sheaf.IsLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (AddCommGrpCat.{w}) Y.smallEtaleTopology X.smallEtaleTopology).obj F))

/- Lemma 59.64.3 (4): finite étale pushforward preserves finite locally
constant abelian-group-valued sheaves on the small étale site. -/
@[stacks 095B]
#check
  (AlgebraicGeometry.Scheme.finiteEtale_pushforward_isFiniteLocallyConstantAddCommGrp :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
      [∀ U : X.Etale,
        HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{w}]
      [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
      [∀ U : Y.Etale,
        HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{w}]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
      [Sheaf.IsFiniteLocallyConstantAddCommGrp F],
    Sheaf.IsFiniteLocallyConstantAddCommGrp
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (AddCommGrpCat.{w}) Y.smallEtaleTopology X.smallEtaleTopology).obj F))

/- Lemma 59.64.3 (5): finite étale pushforward preserves locally constant
sheaves of Λ-modules on the small étale site. -/
@[stacks 095B]
#check
  (AlgebraicGeometry.Scheme.finiteEtale_pushforward_isLocallyConstantModule :
    ∀ {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] (f : X ⟶ Y)
      [IsFinite f] [Etale f]
      [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ U : X.Etale,
        HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ U : Y.Etale,
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
      [Sheaf.IsLocallyConstant F],
    Sheaf.IsLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) Y.smallEtaleTopology X.smallEtaleTopology).obj F))

/- Lemma 59.64.3 (6): finite étale pushforward preserves finite-type locally
constant sheaves of Λ-modules on the small étale site. -/
@[stacks 095B]
#check
  (AlgebraicGeometry.Scheme.finiteEtale_pushforward_isFiniteTypeLocallyConstantModule :
    ∀ {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] (f : X ⟶ Y)
      [IsFinite f] [Etale f]
      [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ U : X.Etale,
        HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ U : Y.Etale,
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
      [Sheaf.IsFiniteTypeLocallyConstantModule F],
    Sheaf.IsFiniteTypeLocallyConstantModule
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) Y.smallEtaleTopology X.smallEtaleTopology).obj F))
