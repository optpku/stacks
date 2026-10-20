module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Map
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero Maps Between Left Resolutions

The zero morphism between two resolving models lies over the zero morphism between their target
objects.  This file supplies that construction under only zero-morphism hypotheses, together
with its computation, transport, and composition API.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.LeftResolution.Map

open Limits

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂} [Φ.functor.PreservesZeroMorphisms]

variable {X Y Z : C₂} {g : Y ⟶ Z}
  {R : Φ.LeftResolution X} {S : Φ.LeftResolution Y} {U : Φ.LeftResolution Z}

/-- Zero model morphisms satisfy the left-resolution comparison square over the zero target
morphism. -/
theorem zero_naturality (R : Φ.LeftResolution X) (S : Φ.LeftResolution Y) :
    Φ.functor.map (0 : R.model ⟶ S.model) ≫ S.comparison =
      R.comparison ≫ (0 : X ⟶ Y) := sorry

/-- The zero map between two left resolutions, lying over the zero target morphism. -/
@[stacks 0GSL "zero map of left resolutions"]
def zero (R : Φ.LeftResolution X) (S : Φ.LeftResolution Y) :
    Map (0 : X ⟶ Y) R S where
  modelHom := 0
  comparison_naturality := zero_naturality R S

/-- The zero left-resolution map has zero model morphism. -/
@[simp]
theorem zero_modelHom (R : Φ.LeftResolution X) (S : Φ.LeftResolution Y) :
    (zero R S).modelHom = 0 := sorry

/-- The zero left-resolution map has zero target-model morphism. -/
@[simp]
theorem zero_hom (R : Φ.LeftResolution X) (S : Φ.LeftResolution Y) :
    (zero R S).hom = 0 := sorry

/-- Reindexing a zero left-resolution map along an equality from zero to zero does not change
the map. -/
@[simp]
theorem reindex_zero (R : Φ.LeftResolution X) (S : Φ.LeftResolution Y)
    (e : (0 : X ⟶ Y) = 0) :
    reindex e (zero R S) = zero R S := sorry

/-- Composing a zero left-resolution map on the left gives the zero map after reindexing the
composite zero morphism. -/
@[simp]
theorem zero_comp (m : Map g S U) :
    reindex Limits.zero_comp (comp (zero R S) m) = zero R U := sorry

/-- Composing a zero left-resolution map on the right gives the zero map after reindexing the
composite zero morphism. -/
@[simp]
theorem comp_zero {f : X ⟶ Y} (m : Map f R S) :
    reindex Limits.comp_zero (comp m (zero S U)) = zero R U := sorry

end CategoryTheory.LocalizerMorphism.LeftResolution.Map


