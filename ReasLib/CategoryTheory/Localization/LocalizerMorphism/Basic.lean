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
# Basic API for Localizer Morphisms

This leaf records structural instances for Mathlib localizer-morphism constructors.  In
particular, a morphism built from equality with an inverse-image morphism property is induced in
the sense expected by the resolution and derivability APIs.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable {W₁' : MorphismProperty C₁}

/-- The identity functor regarded as a localizer morphism along an inclusion of morphism
properties. -/
@[simps, stacks 0GSL "monotonicity of localization systems"]
def ofLE (h : W₁ ≤ W₁') : LocalizerMorphism W₁ W₁' where
  functor := 𝟭 C₁
  map := h

end LocalizerMorphism

namespace LocalizerMorphism.ofEq

/-- A localizer morphism defined by equality with an inverse-image property is induced. -/
@[stacks 0GSL "equality-defined localizer morphisms are induced"]
instance isInduced {F : C₁ ⥤ C₂} (hW : W₁ = W₂.inverseImage F) :
    (LocalizerMorphism.ofEq hW).IsInduced := sorry

end LocalizerMorphism.ofEq



end CategoryTheory
