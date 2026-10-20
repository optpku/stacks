/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Comparison
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans.HomFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity and composition coherence for locally induced two-fibre-product maps

The selected map action preserves identities and composition up to the canonical comparisons
obtained from cospan forgetting and the explicit pseudo-pullback action.
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

/-- The map induced by the identity cospan transformation is the identity. -/
theorem map.id (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    map (Bicategory.CospanTransform.id F G) = 𝟙 (apex F G) := sorry

/-- Maps of locally induced two-fibre products respect composition of cospan transformations. -/
theorem map.comp
    {X₃ Y₃ S₃ : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂)
    (φ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₂ G₂ F₃ G₃) :
    map (ψ.comp φ) = map ψ ≫ map φ := sorry

/-- Canonical componentwise isomorphism for identity preservation. It first compares the
forgotten image of the identity cospan transformation with the ambient identity transformation,
then uses the explicit pseudo-pullback identity coherence. -/
@[stacks 0040 "identity comparison for locally induced two-fibre-product maps"]
noncomputable def map.idIso (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    map (Bicategory.CospanTransform.id F G) ≅ 𝟙 (apex F G) :=
  (Q _ _).isoMk
    (BasedCategory.PseudoPullback.map.iso
        (CospanTransform.forget.idIso F G) ≪≫
      BasedCategory.PseudoPullback.map.idIso F.obj G.obj)

/-- Forgetting the forward identity comparison recovers the composite of the forgetful
pseudofunctor comparison with the explicit pseudo-pullback identity coherence. -/
@[simp]
theorem map.idIso.hom (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    (map.idIso F G).hom.hom =
      (BasedCategory.PseudoPullback.map.iso
          (CospanTransform.forget.idIso F G) ≪≫
        BasedCategory.PseudoPullback.map.idIso F.obj G.obj).hom := sorry

/-- Forgetting the inverse identity comparison recovers the inverse composite of the forgetful
pseudofunctor comparison with the explicit pseudo-pullback identity coherence. -/
@[simp]
theorem map.idIso.inv (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    (map.idIso F G).inv.hom =
      (BasedCategory.PseudoPullback.map.iso
          (CospanTransform.forget.idIso F G) ≪≫
        BasedCategory.PseudoPullback.map.idIso F.obj G.obj).inv := sorry

/-- Canonical componentwise isomorphism for composition preservation. Pseudofunctoriality of
forgetting cospans and explicit pseudo-pullback composition coherence are kept as two reusable
factors. -/
@[stacks 0040 "composition comparison for locally induced two-fibre-product maps"]
noncomputable def map.compIso
    {X₃ Y₃ S₃ : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂)
    (φ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₂ G₂ F₃ G₃) :
    map (ψ.comp φ) ≅ map ψ ≫ map φ :=
  (Q _ _).isoMk
    (BasedCategory.PseudoPullback.map.iso
        (CospanTransform.forget.compIso ψ φ) ≪≫
      BasedCategory.PseudoPullback.map.compIso
        (CospanTransform.forget ψ) (CospanTransform.forget φ))

/-- Forgetting the forward composition comparison recovers the forgetful pseudofunctor
comparison followed by the explicit pseudo-pullback composition coherence. -/
@[simp]
theorem map.compIso.hom
    {X₃ Y₃ S₃ : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂)
    (φ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₂ G₂ F₃ G₃) :
    (map.compIso ψ φ).hom.hom =
      (BasedCategory.PseudoPullback.map.iso
          (CospanTransform.forget.compIso ψ φ) ≪≫
        BasedCategory.PseudoPullback.map.compIso
          (CospanTransform.forget ψ) (CospanTransform.forget φ)).hom := sorry

/-- Forgetting the inverse composition comparison recovers the inverse of the forgetful
pseudofunctor comparison followed by the explicit pseudo-pullback composition coherence. -/
@[simp]
theorem map.compIso.inv
    {X₃ Y₃ S₃ : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂)
    (φ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₂ G₂ F₃ G₃) :
    (map.compIso ψ φ).inv.hom =
      (BasedCategory.PseudoPullback.map.iso
          (CospanTransform.forget.compIso ψ φ) ≪≫
        BasedCategory.PseudoPullback.map.compIso
          (CospanTransform.forget ψ) (CospanTransform.forget φ)).inv := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
