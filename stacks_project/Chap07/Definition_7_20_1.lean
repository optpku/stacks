/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Precoverage.Cocontinuous
import StacksCheckRecall

@[expose] public section

universe u₁ u₂ v₁ v₂

open CategoryTheory

/- Definition 7.20.1: a functor u : C ⥤ D of sites is cocontinuous when every
covering {Vⱼ ⟶ u(U)} of D admits a covering {Uᵢ ⟶ U} of C whose image family
{u(Uᵢ) ⟶ u(U)} refines it. The image family need not itself be a covering of D. -/
@[stacks 00XJ] #check
  (CategoryTheory.Functor.Precoverage.IsCocontinuous :
    ∀ {C : Type u₁} [CategoryTheory.Category.{v₁} C]
      {D : Type u₂} [CategoryTheory.Category.{v₂} D],
      (C ⥤ D) → CategoryTheory.Precoverage C → CategoryTheory.Precoverage D → Prop)
