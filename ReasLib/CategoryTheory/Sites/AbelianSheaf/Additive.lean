/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Additive functors on sheaves of abelian groups

This module records coefficient-level additivity of continuous direct image.  Global sections are
owned by `CategoryTheory.Sheaf.globalSections_additive`; keeping the direct-image owner here gives
downstream site arguments one small import without introducing ringed-site dependencies.
-/

open CategoryTheory

universe z uC vC uD vD

namespace CategoryTheory

namespace Functor

/-- Continuous direct image of sheaves of abelian groups is additive. -/
@[stacks 0D6H "additivity of abelian-sheaf direct image"]
instance sheafPushforwardContinuous_additive
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] :
    (F.sheafPushforwardContinuous _root_.AddCommGrpCat.{z} J K).Additive := sorry

/-- Continuous inverse image of sheaves of abelian groups is additive by adjunction. -/
@[stacks 0D6H "additivity of abelian-sheaf inverse image"]
instance sheafPullback_additive
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]
    [(F.sheafPushforwardContinuous _root_.AddCommGrpCat.{z} J K).IsRightAdjoint] :
    (F.sheafPullback _root_.AddCommGrpCat.{z} J K).Additive := sorry

/-- The chosen left adjoint of continuous abelian-sheaf direct image is additive. -/
@[stacks 0D6H "additivity of the chosen abelian-sheaf inverse image"]
instance sheafPushforwardContinuous_leftAdjoint_additive
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]
    [(F.sheafPushforwardContinuous _root_.AddCommGrpCat.{z} J K).IsRightAdjoint] :
    (Functor.leftAdjoint
      (F.sheafPushforwardContinuous _root_.AddCommGrpCat.{z} J K)).Additive := sorry

end Functor

end CategoryTheory
