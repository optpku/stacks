/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Map.Zero
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Calculus for Maps Between Left Resolutions

Maps between left resolutions form a dependent additive family over morphisms in the target
category.  Addition, negation, and subtraction therefore change the target morphism indexing the
map.  The reindexing lemmas in this file make those changes explicit, and the composition lemmas
record bilinearity without imposing a spurious additive structure on an affine fiber.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.LeftResolution.Map

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Preadditive C₁] [Preadditive C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂} [Φ.functor.Additive]

variable {X Y Z : C₂} {f g : X ⟶ Y} {h k : Y ⟶ Z}
  {R : Φ.LeftResolution X} {S : Φ.LeftResolution Y} {U : Φ.LeftResolution Z}

/-- Sums of model morphisms satisfy the comparison square over the sum of their target
morphisms. -/
theorem add_naturality (m : Map f R S) (n : Map g R S) :
    Φ.functor.map (m.modelHom + n.modelHom) ≫ S.comparison =
      R.comparison ≫ (f + g) := sorry

/-- Add two maps between the same left resolutions, adding their target morphisms as well. -/
@[stacks 0GSL "addition of maps of left resolutions"]
def add (m : Map f R S) (n : Map g R S) : Map (f + g) R S where
  modelHom := m.modelHom + n.modelHom
  comparison_naturality := add_naturality m n

/-- Addition of left-resolution maps adds their model morphisms. -/
@[simp]
theorem add_modelHom (m : Map f R S) (n : Map g R S) :
    (add m n).modelHom = m.modelHom + n.modelHom := sorry

/-- Addition of left-resolution maps adds their target-model morphisms. -/
@[simp]
theorem add_hom (m : Map f R S) (n : Map g R S) :
    (add m n).hom = m.hom + n.hom := sorry

/-- Negated model morphisms satisfy the comparison square over the negated target morphism. -/
theorem neg_naturality (m : Map f R S) :
    Φ.functor.map (-m.modelHom) ≫ S.comparison = R.comparison ≫ (-f) := sorry

/-- Negate a map between left resolutions, negating its target morphism as well. -/
@[stacks 0GSL "negation of maps of left resolutions"]
def neg (m : Map f R S) : Map (-f) R S where
  modelHom := -m.modelHom
  comparison_naturality := neg_naturality m

/-- Negation of a left-resolution map negates its model morphism. -/
@[simp]
theorem neg_modelHom (m : Map f R S) : (neg m).modelHom = -m.modelHom := sorry

/-- Negation of a left-resolution map negates its target-model morphism. -/
@[simp]
theorem neg_hom (m : Map f R S) : (neg m).hom = -m.hom := sorry

/-- Differences of model morphisms satisfy the comparison square over the difference of their
target morphisms. -/
theorem sub_naturality (m : Map f R S) (n : Map g R S) :
    Φ.functor.map (m.modelHom - n.modelHom) ≫ S.comparison =
      R.comparison ≫ (f - g) := sorry

/-- Subtract two maps between the same left resolutions, subtracting their target morphisms as
well. -/
@[stacks 0GSL "subtraction of maps of left resolutions"]
def sub (m : Map f R S) (n : Map g R S) : Map (f - g) R S where
  modelHom := m.modelHom - n.modelHom
  comparison_naturality := sub_naturality m n

/-- Subtraction of left-resolution maps subtracts their model morphisms. -/
@[simp]
theorem sub_modelHom (m : Map f R S) (n : Map g R S) :
    (sub m n).modelHom = m.modelHom - n.modelHom := sorry

/-- Subtraction of left-resolution maps subtracts their target-model morphisms. -/
@[simp]
theorem sub_hom (m : Map f R S) (n : Map g R S) :
    (sub m n).hom = m.hom - n.hom := sorry

/-- Reindexing commutes with addition of maps between left resolutions. -/
@[simp]
theorem reindex_add {f' g' : X ⟶ Y} (ef : f = f') (eg : g = g')
    (m : Map f R S) (n : Map g R S) :
    reindex (congrArg₂ (fun (a b : X ⟶ Y) ↦ a + b) ef eg) (add m n) =
      add (reindex ef m) (reindex eg n) := sorry

/-- Reindexing commutes with negation of maps between left resolutions. -/
@[simp]
theorem reindex_neg {f' : X ⟶ Y} (e : f = f') (m : Map f R S) :
    reindex (congrArg (fun a : X ⟶ Y ↦ -a) e) (neg m) =
      neg (reindex e m) := sorry

/-- Reindexing commutes with subtraction of maps between left resolutions. -/
@[simp]
theorem reindex_sub {f' g' : X ⟶ Y} (ef : f = f') (eg : g = g')
    (m : Map f R S) (n : Map g R S) :
    reindex (congrArg₂ (fun (a b : X ⟶ Y) ↦ a - b) ef eg) (sub m n) =
      sub (reindex ef m) (reindex eg n) := sorry

/-- Composition distributes over addition in the left map, after reindexing the target
morphism. -/
@[simp]
theorem add_comp (m : Map f R S) (n : Map g R S) (q : Map h S U) :
    reindex (Preadditive.add_comp X Y Z f g h) (comp (add m n) q) =
      add (comp m q) (comp n q) := sorry

/-- Composition distributes over addition in the right map, after reindexing the target
morphism. -/
@[simp]
theorem comp_add (m : Map f R S) (n : Map h S U) (q : Map k S U) :
    reindex (Preadditive.comp_add X Y Z f h k) (comp m (add n q)) =
      add (comp m n) (comp m q) := sorry

/-- Composition commutes with negation in the left map, after reindexing the target morphism. -/
@[simp]
theorem neg_comp (m : Map f R S) (n : Map h S U) :
    reindex (Preadditive.neg_comp f h) (comp (neg m) n) =
      neg (comp m n) := sorry

/-- Composition commutes with negation in the right map, after reindexing the target morphism. -/
@[simp]
theorem comp_neg (m : Map f R S) (n : Map h S U) :
    reindex (Preadditive.comp_neg f h) (comp m (neg n)) =
      neg (comp m n) := sorry

/-- Composition distributes over subtraction in the left map, after reindexing the target
morphism. -/
@[simp]
theorem sub_comp (m : Map f R S) (n : Map g R S) (q : Map h S U) :
    reindex (Preadditive.sub_comp f g h) (comp (sub m n) q) =
      sub (comp m q) (comp n q) := sorry

/-- Composition distributes over subtraction in the right map, after reindexing the target
morphism. -/
@[simp]
theorem comp_sub (m : Map f R S) (n : Map h S U) (q : Map k S U) :
    reindex (Preadditive.comp_sub f h k) (comp m (sub n q)) =
      sub (comp m n) (comp m q) := sorry

end CategoryTheory.LocalizerMorphism.LeftResolution.Map


