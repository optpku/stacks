/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Total.Functorial
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Total.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive Functors of Total Left Resolutions

A functorial left resolution whose base and model functors are additive assembles to an additive
functor into the total resolution category. This lets downstream code use the ordinary additive
functor API without unpacking dependent resolution maps.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.LocalizerMorphism.LeftResolution.FunctorialAlong.total

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂} [Φ.functor.Additive]
  {F : D ⥤ C₂} [F.Additive]

/-- The total functor associated to additive functorial left-resolution data is additive. -/
@[stacks 0GSL "additivity of a functorial total left resolution"]
instance functorAdditive (R : FunctorialAlong Φ F) [R.model.Additive] :
    R.total.Additive := sorry

end CategoryTheory.LocalizerMorphism.LeftResolution.FunctorialAlong.total
