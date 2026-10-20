/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map.Action
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map.Projections
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Target-comparison coherence for locally induced two-fibre-product maps

The target comparison of an induced map is the canonical pasting between its two projection
legs. Its boundary equation and naturality under modifications are exposed directly.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced.TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [Projections.Has (P := P) (Q := Q)]
variable [Q.IsClosedUnderIsomorphisms]
variable [Projections.IsDetected (P := P) (Q := Q)]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : Bicategory.LocallyInducedBicategory
  (BasedCategory.{max v vB, max w (max u (max v vB))} C)
  (fun X : P.FullSubbicategory ↦ X.1) Q}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}
variable {ψ φ : Bicategory.CospanTransform
  (B := Bicategory.LocallyInducedBicategory
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)
    (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂}

/-- The target comparison whiskered by the induced map of locally induced two-fibre products. -/
@[stacks 0040 "target comparison for a locally induced two-fibre-product map"]
noncomputable def map.comparisonIso
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    (map ψ ≫ fst F₂ G₂) ≫ F₂ ≅ (map ψ ≫ snd F₂ G₂) ≫ G₂ :=
  (α_ (map ψ) (fst F₂ G₂) F₂) ≪≫
    Bicategory.whiskerLeftIso (map ψ)
        (_root_.CategoryTheory.LocallyInduced.TwoFibreProduct.comparisonIso F₂ G₂) ≪≫
      (α_ (map ψ) (snd F₂ G₂) G₂).symm

/-- Forgetting the forward target comparison recovers the explicit based pseudo-pullback
target comparison. -/
@[simp]
theorem map.comparisonIso.hom
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    (map.comparisonIso ψ).hom.hom =
      (BasedCategory.PseudoPullback.map.comparisonIso
        (CospanTransform.forget ψ)).hom := sorry

/-- Forgetting the inverse target comparison recovers the inverse explicit based
pseudo-pullback target comparison. -/
@[simp]
theorem map.comparisonIso.inv
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    (map.comparisonIso ψ).inv.hom =
      (BasedCategory.PseudoPullback.map.comparisonIso
        (CospanTransform.forget ψ)).inv := sorry

/-- Naturality of the locally induced target comparison under a cospan transformation,
expressed as the symmetric boundary pasting through the projection comparisons. -/
theorem map.comparisonIso.equation
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    map.comparisonIso ψ =
      Bicategory.whiskerRightIso (map.fstIso ψ) F₂ ≪≫
        (α_ (fst F₁ G₁) ψ.left F₂) ≪≫
          Bicategory.whiskerLeftIso (fst F₁ G₁) ψ.leftIso ≪≫
            (α_ (fst F₁ G₁) F₁ ψ.base).symm ≪≫
              Bicategory.whiskerRightIso
                (_root_.CategoryTheory.LocallyInduced.TwoFibreProduct.comparisonIso F₁ G₁)
                ψ.base ≪≫
                (α_ (snd F₁ G₁) G₁ ψ.base) ≪≫
                  Bicategory.whiskerLeftIso
                    (snd F₁ G₁) ψ.rightIso.symm ≪≫
                    (α_ (snd F₁ G₁) ψ.right G₂).symm ≪≫
                      Bicategory.whiskerRightIso
                        (map.sndIso ψ).symm G₂ := sorry

/-- The target comparison is `2`-natural in modifications of selected cospan
transformations. -/
theorem map.comparisonIso.naturality
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    ((map₂ Γ ▷ fst F₂ G₂) ▷ F₂) ≫ (map.comparisonIso φ).hom =
      (map.comparisonIso ψ).hom ≫
        ((map₂ Γ ▷ snd F₂ G₂) ▷ G₂) := sorry

/-- The inverse target comparison is `2`-natural in modifications of selected cospan
transformations. -/
theorem map.comparisonIso.invNaturality
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    (map.comparisonIso ψ).inv ≫
        ((map₂ Γ ▷ fst F₂ G₂) ▷ F₂) =
      ((map₂ Γ ▷ snd F₂ G₂) ▷ G₂) ≫
        (map.comparisonIso φ).inv := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
