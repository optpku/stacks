/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map.Zero
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Calculus for Maps Between Right Resolutions

Maps between right resolutions form a dependent additive family over morphisms in the target
category.  Addition, negation, and subtraction therefore change the target morphism indexing the
map.  The reindexing lemmas in this file make those changes explicit, and the composition lemmas
record bilinearity without imposing a spurious additive structure on an affine fiber.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.RightResolution.Map

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Preadditive C₁] [Preadditive C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂} [Φ.functor.Additive]

variable {X Y Z : C₂} {f g : X ⟶ Y} {h k : Y ⟶ Z}
  {R : Φ.RightResolution X} {S : Φ.RightResolution Y} {U : Φ.RightResolution Z}

/-- Sums of model morphisms satisfy the comparison square over the sum of their target
morphisms. -/
theorem add_naturality (m : Map f R S) (n : Map g R S) :
    R.comparison ≫ Φ.functor.map (m.modelHom + n.modelHom) =
      (f + g) ≫ S.comparison := by
  rw [Functor.map_add, Preadditive.comp_add, m.comparison_naturality,
    n.comparison_naturality, Preadditive.add_comp]

/-- Add two maps between the same right resolutions, adding their target morphisms as well. -/
@[stacks 0GSL "addition of maps of right resolutions"]
def add (m : Map f R S) (n : Map g R S) : Map (f + g) R S where
  modelHom := m.modelHom + n.modelHom
  comparison_naturality := add_naturality m n

/-- Addition of right-resolution maps adds their model morphisms. -/
@[simp]
theorem add_modelHom (m : Map f R S) (n : Map g R S) :
    (add m n).modelHom = m.modelHom + n.modelHom := rfl

/-- Addition of right-resolution maps adds their target-model morphisms. -/
@[simp]
theorem add_hom (m : Map f R S) (n : Map g R S) :
    (add m n).hom = m.hom + n.hom := Φ.functor.map_add

/-- Negated model morphisms satisfy the comparison square over the negated target morphism. -/
theorem neg_naturality (m : Map f R S) :
    R.comparison ≫ Φ.functor.map (-m.modelHom) = (-f) ≫ S.comparison := by
  rw [Functor.map_neg, Preadditive.comp_neg, m.comparison_naturality, Preadditive.neg_comp]

/-- Negate a map between right resolutions, negating its target morphism as well. -/
@[stacks 0GSL "negation of maps of right resolutions"]
def neg (m : Map f R S) : Map (-f) R S where
  modelHom := -m.modelHom
  comparison_naturality := neg_naturality m

/-- Negation of a right-resolution map negates its model morphism. -/
@[simp]
theorem neg_modelHom (m : Map f R S) : (neg m).modelHom = -m.modelHom := rfl

/-- Negation of a right-resolution map negates its target-model morphism. -/
@[simp]
theorem neg_hom (m : Map f R S) : (neg m).hom = -m.hom := Φ.functor.map_neg

/-- Differences of model morphisms satisfy the comparison square over the difference of their
target morphisms. -/
theorem sub_naturality (m : Map f R S) (n : Map g R S) :
    R.comparison ≫ Φ.functor.map (m.modelHom - n.modelHom) =
      (f - g) ≫ S.comparison := by
  rw [Functor.map_sub, Preadditive.comp_sub, m.comparison_naturality,
    n.comparison_naturality, Preadditive.sub_comp]

/-- Subtract two maps between the same right resolutions, subtracting their target morphisms as
well. -/
@[stacks 0GSL "subtraction of maps of right resolutions"]
def sub (m : Map f R S) (n : Map g R S) : Map (f - g) R S where
  modelHom := m.modelHom - n.modelHom
  comparison_naturality := sub_naturality m n

/-- Subtraction of right-resolution maps subtracts their model morphisms. -/
@[simp]
theorem sub_modelHom (m : Map f R S) (n : Map g R S) :
    (sub m n).modelHom = m.modelHom - n.modelHom := rfl

/-- Subtraction of right-resolution maps subtracts their target-model morphisms. -/
@[simp]
theorem sub_hom (m : Map f R S) (n : Map g R S) :
    (sub m n).hom = m.hom - n.hom := Φ.functor.map_sub

/-- Reindexing commutes with addition of maps between right resolutions. -/
@[simp]
theorem reindex_add {f' g' : X ⟶ Y} (ef : f = f') (eg : g = g')
    (m : Map f R S) (n : Map g R S) :
    reindex (congrArg₂ (fun (a b : X ⟶ Y) ↦ a + b) ef eg) (add m n) =
      add (reindex ef m) (reindex eg n) := rfl

/-- Reindexing commutes with negation of maps between right resolutions. -/
@[simp]
theorem reindex_neg {f' : X ⟶ Y} (e : f = f') (m : Map f R S) :
    reindex (congrArg (fun a : X ⟶ Y ↦ -a) e) (neg m) =
      neg (reindex e m) := rfl

/-- Reindexing commutes with subtraction of maps between right resolutions. -/
@[simp]
theorem reindex_sub {f' g' : X ⟶ Y} (ef : f = f') (eg : g = g')
    (m : Map f R S) (n : Map g R S) :
    reindex (congrArg₂ (fun (a b : X ⟶ Y) ↦ a - b) ef eg) (sub m n) =
      sub (reindex ef m) (reindex eg n) := rfl

/-- Composition distributes over addition in the left map, after reindexing the target
morphism. -/
@[simp]
theorem add_comp (m : Map f R S) (n : Map g R S) (q : Map h S U) :
    reindex (Preadditive.add_comp X Y Z f g h) (comp (add m n) q) =
      add (comp m q) (comp n q) := by
  apply Map.ext
  exact Preadditive.add_comp _ _ _ _ _ _

/-- Composition distributes over addition in the right map, after reindexing the target
morphism. -/
@[simp]
theorem comp_add (m : Map f R S) (n : Map h S U) (q : Map k S U) :
    reindex (Preadditive.comp_add X Y Z f h k) (comp m (add n q)) =
      add (comp m n) (comp m q) := by
  apply Map.ext
  exact Preadditive.comp_add _ _ _ _ _ _

/-- Composition commutes with negation in the left map, after reindexing the target morphism. -/
@[simp]
theorem neg_comp (m : Map f R S) (n : Map h S U) :
    reindex (Preadditive.neg_comp f h) (comp (neg m) n) =
      neg (comp m n) := by
  apply Map.ext
  exact Preadditive.neg_comp _ _

/-- Composition commutes with negation in the right map, after reindexing the target morphism. -/
@[simp]
theorem comp_neg (m : Map f R S) (n : Map h S U) :
    reindex (Preadditive.comp_neg f h) (comp m (neg n)) =
      neg (comp m n) := by
  apply Map.ext
  exact Preadditive.comp_neg _ _

/-- Composition distributes over subtraction in the left map, after reindexing the target
morphism. -/
@[simp]
theorem sub_comp (m : Map f R S) (n : Map g R S) (q : Map h S U) :
    reindex (Preadditive.sub_comp f g h) (comp (sub m n) q) =
      sub (comp m q) (comp n q) := by
  apply Map.ext
  exact Preadditive.sub_comp _ _ _

/-- Composition distributes over subtraction in the right map, after reindexing the target
morphism. -/
@[simp]
theorem comp_sub (m : Map f R S) (n : Map h S U) (q : Map k S U) :
    reindex (Preadditive.comp_sub f h k) (comp m (sub n q)) =
      sub (comp m n) (comp m q) := by
  apply Map.ext
  exact Preadditive.comp_sub _ _ _

end CategoryTheory.LocalizerMorphism.RightResolution.Map


