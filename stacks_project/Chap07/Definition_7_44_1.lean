/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
import StacksCheckRecall

@[expose] public section

open CategoryTheory Functor

universe u₁ u₂ v₁ v₂ w t

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type w} [Category.{t} A]
variable (u : C ⥤ D)

/- Definition 7.44.1 (1): let f : D → C be a morphism of sites given by a functor
u : C ⥤ D. The pushforward of presheaves of algebraic structures is the
precomposition functor u^p with object formula u^p F(U) = F(u U). This is
(whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op : (Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A). -/
@[stacks 00YS] #check ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op : (Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A))

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]

/- Definition 7.44.1 (2): for the same morphism of sites f : D → C given by u,
the pushforward of sheaves of algebraic structures is the same precomposition
rule f_* F(U) = F(u U). This is the continuous sheaf pushforward
u.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A. -/
@[stacks 00YS] #check (u.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A)

#check (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K :
    u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A ≅
      sheafToPresheaf K A ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op)
