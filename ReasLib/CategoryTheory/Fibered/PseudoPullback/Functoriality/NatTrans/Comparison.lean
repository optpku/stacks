/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.Projection
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Whiskering
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison pasting for explicit pseudo-pullback maps

This leaf owns the target comparison whiskered by an induced pseudo-pullback map, its source-side
boundary-pasting formula, and the objectwise component calculations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}

/-- The target comparison, whiskered by an induced pseudo-pullback map. This is the short
source-facing owner for the upper comparison in the mapped square. -/
@[stacks 0040 "target comparison for a map of explicit pseudo-pullbacks"]
def map.comparisonIso
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    (map ψ ⋙ fst F₂ G₂) ⋙ F₂ ≅ (map ψ ⋙ snd F₂ G₂) ⋙ G₂ :=
  eqToIso (BasedFunctor.comp_assoc (map ψ) (fst F₂ G₂) F₂) ≪≫
    BasedNatIso.whiskerLeft
      (map ψ) (_root_.CategoryTheory.BasedCategory.PseudoPullback.comparisonIso F₂ G₂) ≪≫
      (eqToIso (BasedFunctor.comp_assoc (map ψ) (snd F₂ G₂) G₂)).symm

/-- The mapped target comparison is the symmetric boundary pasting through the source
comparison and the two naturality isomorphisms of the cospan transformation.

Proof strategy: pass to underlying natural transformations and evaluate at a pseudo-pullback
object. Both sides reduce to naturality of `ψ.leftIso` and `ψ.rightIso` around the explicit
three-step comparison stored by `mapObj`. -/
theorem map.comparisonIso.equation
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    map.comparisonIso ψ =
      BasedNatIso.whiskerRight (map.fstIso ψ) F₂ ≪≫
        eqToIso (BasedFunctor.comp_assoc (fst F₁ G₁) ψ.left F₂) ≪≫
          BasedNatIso.whiskerLeft (fst F₁ G₁) ψ.leftIso ≪≫
            (eqToIso (BasedFunctor.comp_assoc (fst F₁ G₁) F₁ ψ.base)).symm ≪≫
              BasedNatIso.whiskerRight
                (_root_.CategoryTheory.BasedCategory.PseudoPullback.comparisonIso F₁ G₁)
                ψ.base ≪≫
                eqToIso (BasedFunctor.comp_assoc (snd F₁ G₁) G₁ ψ.base) ≪≫
                  BasedNatIso.whiskerLeft (snd F₁ G₁) ψ.rightIso.symm ≪≫
                    (eqToIso (BasedFunctor.comp_assoc (snd F₁ G₁) ψ.right G₂)).symm ≪≫
                      BasedNatIso.whiskerRight (map.sndIso ψ).symm G₂ := sorry
/-- The forward component of the mapped comparison is the target pseudo-pullback comparison. -/
@[simp]
theorem map.comparisonIso.hom.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map.comparisonIso ψ).hom.toNatTrans.app P =
      (_root_.CategoryTheory.BasedCategory.PseudoPullback.comparisonIso F₂ G₂).hom.toNatTrans.app ((map ψ).obj P) := sorry

/-- The inverse component of the mapped comparison is the inverse target comparison. -/
@[simp]
theorem map.comparisonIso.inv.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map.comparisonIso ψ).inv.toNatTrans.app P =
      (_root_.CategoryTheory.BasedCategory.PseudoPullback.comparisonIso F₂ G₂).inv.toNatTrans.app ((map ψ).obj P) := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
