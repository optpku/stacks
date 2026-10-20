/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Preadditive Localizer Morphisms

This file records the additive functor instances carried by the standard constructors for
localizer morphisms.  Naming these definally evident instances keeps downstream resolution APIs
independent of unfolding choices made by typeclass search.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.LocalizerMorphism

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₃ : MorphismProperty C₃}

namespace id

/-- The functor underlying the identity localizer morphism is additive. -/
instance functorAdditive : (LocalizerMorphism.id W₁).functor.Additive := sorry

end id

namespace ofEq

/-- An equality-induced localizer morphism inherits additivity from its underlying functor. -/
instance functorAdditive {F : C₁ ⥤ C₂} [F.Additive]
    (hW : W₁ = W₂.inverseImage F) : (LocalizerMorphism.ofEq hW).functor.Additive := sorry

end ofEq

namespace ofLE

/-- The functor underlying a monotonicity localizer morphism is additive. -/
instance functorAdditive {W₁' : MorphismProperty C₁} (h : W₁ ≤ W₁') :
    (LocalizerMorphism.ofLE h).functor.Additive := sorry

end ofLE

namespace comp

/-- A composite localizer morphism has an additive underlying functor when both factors do. -/
instance functorAdditive (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) [Φ.functor.Additive] [Ψ.functor.Additive] :
    (Φ.comp Ψ).functor.Additive := sorry

end comp




end CategoryTheory.LocalizerMorphism
