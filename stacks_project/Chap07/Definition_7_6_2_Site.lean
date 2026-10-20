/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.PrecoverageSite

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

#check (@Precoverage.IsSite : ∀ {C : Type u} [Category.{v} C], Precoverage C → Prop)

#check (@Precoverage.IsSite.hasFactoringPullbacks :
  ∀ {C : Type u} [Category.{v} C] (J : Precoverage C) [J.IsSite],
    J.HasFactoringPullbacks)

#check (@Precoverage.IsSite.iff : ∀ {C : Type u} [Category.{v} C] (J : Precoverage C),
  J.IsSite ↔ J.HasIsos ∧ J.HasPullbacks ∧ J.IsStableUnderBind ∧ J.IsStableUnderPullbackArrows)

#check (@Pretopology.instIsSite :
  ∀ {C : Type u} [Category.{v} C] [HasPullbacks C] (P : Pretopology C),
    P.toPrecoverage.IsSite)
