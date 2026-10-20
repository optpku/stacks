/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.ZMod

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

#check (AlgebraicGeometry.Scheme.Etale.zmodSheafPushforward :
  ∀ {A B : Scheme.{u}} (p : A ⟶ B) (n : ℕ),
    Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)))
