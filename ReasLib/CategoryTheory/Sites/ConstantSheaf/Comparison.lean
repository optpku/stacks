/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Constant sheaves and continuous restriction

The sheafification unit induces a canonical comparison from a constant sheaf
to the restriction of a constant sheaf along a continuous functor of sites.
-/

@[expose] public section

noncomputable section

universe uC vC uD vD uA vA

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable (f : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (A : Type uA) [Category.{vA} A] [f.IsContinuous J K]
variable [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The canonical morphism from the constant sheaf with coefficients `E` to the
restriction of that constant sheaf along a continuous functor of sites. -/
def constantSheafRestrictionHom (E : A) :
    (constantSheaf J A).obj E ⟶
      (f.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj E) :=
  ((sheafificationAdjunction J A).homEquiv ((const Cᵒᵖ).obj E)
      ((f.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj E))).symm
    ((constCompWhiskeringLeftIso Cᵒᵖ f.op).inv.app E ≫
      whiskerLeft f.op ((sheafificationAdjunction K A).unit.app ((const Dᵒᵖ).obj E)))

/-- Under the sheafification adjunction, the constant-sheaf restriction
comparison is the restriction of the sheafification unit of the constant presheaf. -/
theorem constantSheafRestrictionHom_homEquiv (E : A) :
    (sheafificationAdjunction J A).homEquiv ((const Cᵒᵖ).obj E)
        ((f.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj E))
        (f.constantSheafRestrictionHom J K A E) =
      (constCompWhiskeringLeftIso Cᵒᵖ f.op).inv.app E ≫
        whiskerLeft f.op ((sheafificationAdjunction K A).unit.app ((const Dᵒᵖ).obj E)) :=
  Equiv.apply_symm_apply _ _

end CategoryTheory.Functor
