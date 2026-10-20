/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map.Functor
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map.Projections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of locally induced two-fibre-product projections

The two projection comparisons are natural in cospan modifications and assemble into natural
isomorphisms on each hom category.
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

/-- The first projection comparison is `2`-natural in modifications of selected cospan
transformations. -/
theorem map₂.fstCommutes
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    map₂ Γ ▷ CategoryTheory.LocallyInduced.TwoFibreProduct.fst F₂ G₂ ≫
        (map.fstIso φ).hom =
      (map.fstIso ψ).hom ≫
        CategoryTheory.LocallyInduced.TwoFibreProduct.fst F₁ G₁ ◁
          Bicategory.CospanTransform.Hom.left Γ := sorry

/-- The second projection comparison is `2`-natural in modifications of selected cospan
transformations. -/
theorem map₂.sndCommutes
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    map₂ Γ ▷ CategoryTheory.LocallyInduced.TwoFibreProduct.snd F₂ G₂ ≫
        (map.sndIso φ).hom =
      (map.sndIso ψ).hom ≫
        CategoryTheory.LocallyInduced.TwoFibreProduct.snd F₁ G₁ ◁
          Bicategory.CospanTransform.Hom.right Γ := sorry

/-- The first-projection comparisons, natural in selected cospan transformations. -/
@[stacks 0040 "natural first-projection comparison for locally induced two-fibre-products"]
noncomputable def map.fstNatIso :
    mapFunctor ⋙ Bicategory.postcomp (apex F₁ G₁) (fst F₂ G₂) ≅
      Bicategory.CospanTransform.leftFunctor ⋙
        Bicategory.precomp X₂ (fst F₁ G₁) :=
  NatIso.ofComponents map.fstIso map₂.fstCommutes

/-- The forward component of `map.fstNatIso` is the canonical first-projection comparison. -/
@[simp]
theorem map.fstNatIso.hom.app
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    map.fstNatIso.hom.app ψ = (map.fstIso ψ).hom := sorry

/-- The inverse component of `map.fstNatIso` is the inverse first-projection comparison. -/
@[simp]
theorem map.fstNatIso.inv.app
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    map.fstNatIso.inv.app ψ = (map.fstIso ψ).inv := sorry

/-- The second-projection comparisons, natural in selected cospan transformations. -/
@[stacks 0040 "natural second-projection comparison for locally induced two-fibre-products"]
noncomputable def map.sndNatIso :
    mapFunctor ⋙ Bicategory.postcomp (apex F₁ G₁) (snd F₂ G₂) ≅
      Bicategory.CospanTransform.rightFunctor ⋙
        Bicategory.precomp Y₂ (snd F₁ G₁) :=
  NatIso.ofComponents map.sndIso map₂.sndCommutes

/-- The forward component of `map.sndNatIso` is the canonical second-projection comparison. -/
@[simp]
theorem map.sndNatIso.hom.app
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    map.sndNatIso.hom.app ψ = (map.sndIso ψ).hom := sorry

/-- The inverse component of `map.sndNatIso` is the inverse second-projection comparison. -/
@[simp]
theorem map.sndNatIso.inv.app
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    map.sndNatIso.inv.app ψ = (map.sndIso ψ).inv := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
