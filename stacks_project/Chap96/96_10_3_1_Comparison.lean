/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.SpacePushforward

/-! # Big-versus-small étale direct-image comparison -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Sheaf.InternalModule
universe u

#check (AlgebraicGeometry.AlgebraicSpace.compareBigSmall :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G)
    (ℱ : Sheaf F.toGroupoids.etaleTopology (Type (u + 1))),
    (restrictEtale G).obj ((etalePushforward f).obj ℱ) ≅
      (sheafPushforwardType f).obj ((restrictEtale F).obj ℱ))

#check (AlgebraicGeometry.AlgebraicSpace.compareBigSmall_modules :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G)
    (ℳ : SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf),
    (restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ) ≅
      (Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ))
