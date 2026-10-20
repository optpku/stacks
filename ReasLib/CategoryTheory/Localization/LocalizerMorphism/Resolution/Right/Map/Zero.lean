/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero Maps Between Right Resolutions

The zero morphism between two resolving models lies over the zero morphism between their target
objects.  This file supplies that construction under only zero-morphism hypotheses, together
with its computation, transport, and composition API.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.RightResolution.Map

open Limits

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂} [Φ.functor.PreservesZeroMorphisms]

variable {X Y Z : C₂} {g : Y ⟶ Z}
  {R : Φ.RightResolution X} {S : Φ.RightResolution Y} {U : Φ.RightResolution Z}

/-- Zero model morphisms satisfy the right-resolution comparison square over the zero target
morphism. -/
theorem zero_naturality (R : Φ.RightResolution X) (S : Φ.RightResolution Y) :
    R.comparison ≫ Φ.functor.map (0 : R.model ⟶ S.model) =
      (0 : X ⟶ Y) ≫ S.comparison := sorry

/-- The zero map between two right resolutions, lying over the zero target morphism. -/
@[stacks 0GSL "zero map of right resolutions"]
def zero (R : Φ.RightResolution X) (S : Φ.RightResolution Y) :
    Map (0 : X ⟶ Y) R S where
  modelHom := 0
  comparison_naturality := zero_naturality R S

/-- The zero right-resolution map has zero model morphism. -/
@[simp]
theorem zero_modelHom (R : Φ.RightResolution X) (S : Φ.RightResolution Y) :
    (zero R S).modelHom = 0 := sorry

/-- The zero right-resolution map has zero target-model morphism. -/
@[simp]
theorem zero_hom (R : Φ.RightResolution X) (S : Φ.RightResolution Y) :
    (zero R S).hom = 0 := sorry

/-- Reindexing a zero right-resolution map along an equality from zero to zero does not change
the map. -/
@[simp]
theorem reindex_zero (R : Φ.RightResolution X) (S : Φ.RightResolution Y)
    (e : (0 : X ⟶ Y) = 0) :
    reindex e (zero R S) = zero R S := sorry

/-- Composing a zero right-resolution map on the left gives the zero map after reindexing the
composite zero morphism. -/
@[simp]
theorem zero_comp (m : Map g S U) :
    reindex Limits.zero_comp (comp (zero R S) m) = zero R U := sorry

/-- Composing a zero right-resolution map on the right gives the zero map after reindexing the
composite zero morphism. -/
@[simp]
theorem comp_zero {f : X ⟶ Y} (m : Map f R S) :
    reindex Limits.comp_zero (comp m (zero S U)) = zero R U := sorry

end CategoryTheory.LocalizerMorphism.RightResolution.Map


