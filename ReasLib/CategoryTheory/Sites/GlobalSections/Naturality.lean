/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.CategoryTheory.Limits.ChangeOfIndex

/-!
# Naturality of global sections under direct image

This module provides the canonical comparison from global sections on a source site to global
sections after direct image along a continuous functor of sites.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe uC vC uD vD uA vA

namespace CategoryTheory

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {A : Type uA} [Category.{vA} A]

namespace Sheaf

/-- Global sections on a site map naturally to global sections after direct image along a
continuous functor of sites. -/
noncomputable def globalSectionsPushforwardNat
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A]
    [HasLimitsOfShape Cᵒᵖ A] [HasLimitsOfShape Dᵒᵖ A] :
    Γ K A ⟶ F.sheafPushforwardContinuous A J K ⋙ Γ J A :=
  (ΓNatIsoLim K A).hom ≫
    Functor.whiskerLeft
      (sheafToPresheaf K A)
      (limitPreNat F.op) ≫
    (Functor.associator
      (sheafToPresheaf K A)
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op)
      (lim : (Cᵒᵖ ⥤ A) ⥤ A)).inv ≫
    Functor.whiskerRight
      ((F.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm.hom)
      (lim : (Cᵒᵖ ⥤ A) ⥤ A) ≫
    (Functor.associator
      (F.sheafPushforwardContinuous A J K)
      (sheafToPresheaf J A)
      (lim : (Cᵒᵖ ⥤ A) ⥤ A)).hom ≫
    Functor.whiskerLeft
      (F.sheafPushforwardContinuous A J K)
      (ΓNatIsoLim J A).inv

end Sheaf

end

end CategoryTheory
