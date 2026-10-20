/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Continuous
import StacksCheckRecall

@[expose] public section

open CategoryTheory Functor

universe u₁ u₂ v₁ v₂ w t

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type w} [Category.{t} A]
variable (u : C ⥤ D)

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]

/- Definition 7.44.1: let f : D → C be a morphism of sites given by u : C ⥤ D.
Pushforward of presheaves of algebraic structures is precomposition by u.op,
with evaluation rule u^p F(U) = F(u U). Pushforward of sheaves has the same
underlying presheaf, hence the same evaluation rule f_* F(U) = F(u U).
The coefficient category A has independent object and morphism universes. -/
@[stacks 00YS] #check
  (CategoryTheory.Functor.sheafPushforwardContinuous_comp_sheafToPresheaf u A J K :
    u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A =
      sheafToPresheaf K A ⋙ (CategoryTheory.Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op)

#check ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op : (Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A))

#check (u.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A)

#check (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K :
    u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A ≅
      sheafToPresheaf K A ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op)
