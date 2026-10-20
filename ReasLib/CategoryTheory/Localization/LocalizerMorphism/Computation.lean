/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Computation for Functors Induced by Localizer Morphisms

This leaf names the canonical comparison isomorphism of a localized functor and exposes the
naturality and conjugation formulas used to compute its map on morphisms coming from the source
localization functor.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.LocalizerMorphism

open Localization

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v₃} D₁] [Category.{v₄} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

/-- The canonical comparison isomorphism for the functor on localizations induced by a
localizer morphism. -/
@[stacks 04VB "comparison isomorphism for an induced localization functor"]
noncomputable def facIso (Φ : LocalizerMorphism W₁ W₂)
    (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂] :
    Φ.functor ⋙ L₂ ≅ L₁ ⋙ Φ.localizedFunctor L₁ L₂ :=
  (LocalizerMorphism.catCommSq Φ L₁ L₂).iso

namespace facIso

/-- Naturality of the forward comparison for a functor induced by a localizer morphism. -/
@[reassoc (attr := simp), stacks 04VB]
theorem hom_naturality (Φ : LocalizerMorphism W₁ W₂)
    (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
    {X Y : C₁} (f : X ⟶ Y) :
    L₂.map (Φ.functor.map f) ≫ (Φ.facIso L₁ L₂).hom.app Y =
      (Φ.facIso L₁ L₂).hom.app X ≫
        (Φ.localizedFunctor L₁ L₂).map (L₁.map f) := sorry

/-- Naturality of the inverse comparison for a functor induced by a localizer morphism. -/
@[reassoc (attr := simp), stacks 04VB]
theorem inv_naturality (Φ : LocalizerMorphism W₁ W₂)
    (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
    {X Y : C₁} (f : X ⟶ Y) :
    (Φ.localizedFunctor L₁ L₂).map (L₁.map f) ≫
        (Φ.facIso L₁ L₂).inv.app Y =
      (Φ.facIso L₁ L₂).inv.app X ≫ L₂.map (Φ.functor.map f) := sorry

end facIso

namespace localizedFunctor

/-- The functor induced by a localizer morphism maps a morphism from the source localization by
conjugating its target-localization image with the canonical comparison isomorphism. -/
@[simp, reassoc (attr := simp), stacks 04VB]
theorem map_localization (Φ : LocalizerMorphism W₁ W₂)
    (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
    {X Y : C₁} (f : X ⟶ Y) :
    (Φ.localizedFunctor L₁ L₂).map (L₁.map f) =
      (Φ.facIso L₁ L₂).inv.app X ≫ L₂.map (Φ.functor.map f) ≫
        (Φ.facIso L₁ L₂).hom.app Y := sorry

/-- The canonical-quotient specialization of `map_localization`. -/
@[stacks 04VB]
theorem map_Q (Φ : LocalizerMorphism W₁ W₂) {X Y : C₁} (f : X ⟶ Y) :
    (Φ.localizedFunctor W₁.Q W₂.Q).map (W₁.Q.map f) =
      (Φ.facIso W₁.Q W₂.Q).inv.app X ≫ W₂.Q.map (Φ.functor.map f) ≫
        (Φ.facIso W₁.Q W₂.Q).hom.app Y := sorry

end localizedFunctor



end CategoryTheory.LocalizerMorphism
