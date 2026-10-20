/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.Projection

/-!
# Projection comparisons for locally induced two-fibre-product maps

The induced map commutes with each pseudo-pullback projection up to the canonical invertible
cell. Forward and inverse ambient computations are exposed for downstream rewriting.
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

/-- The induced map commutes with the first projection up to the canonical invertible cell. -/
@[stacks 0040 "first projection comparison for a locally induced two-fibre-product map"]
noncomputable def map.fstIso
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    map ψ ≫ fst F₂ G₂ ≅ fst F₁ G₁ ≫ ψ.left :=
  (Q _ _).isoMk
    (BasedCategory.PseudoPullback.map.fstIso (CospanTransform.forget ψ))

/-- Forgetting the forward first-projection comparison recovers the corresponding explicit
based pseudo-pullback cell. -/
@[simp]
theorem map.fstIso.hom
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    (map.fstIso ψ).hom.hom =
      (BasedCategory.PseudoPullback.map.fstIso
        (CospanTransform.forget ψ)).hom := sorry

/-- Forgetting the inverse first-projection comparison recovers the inverse explicit based
pseudo-pullback cell. -/
@[simp]
theorem map.fstIso.inv
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    (map.fstIso ψ).inv.hom =
      (BasedCategory.PseudoPullback.map.fstIso
        (CospanTransform.forget ψ)).inv := sorry

/-- The induced map commutes with the second projection up to the canonical invertible cell. -/
@[stacks 0040 "second projection comparison for a locally induced two-fibre-product map"]
noncomputable def map.sndIso
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    map ψ ≫ snd F₂ G₂ ≅ snd F₁ G₁ ≫ ψ.right :=
  (Q _ _).isoMk
    (BasedCategory.PseudoPullback.map.sndIso (CospanTransform.forget ψ))

/-- Forgetting the forward second-projection comparison recovers the corresponding explicit
based pseudo-pullback cell. -/
@[simp]
theorem map.sndIso.hom
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    (map.sndIso ψ).hom.hom =
      (BasedCategory.PseudoPullback.map.sndIso
        (CospanTransform.forget ψ)).hom := sorry

/-- Forgetting the inverse second-projection comparison recovers the inverse explicit based
pseudo-pullback cell. -/
@[simp]
theorem map.sndIso.inv
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    (map.sndIso ψ).inv.hom =
      (BasedCategory.PseudoPullback.map.sndIso
        (CospanTransform.forget ψ)).inv := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
