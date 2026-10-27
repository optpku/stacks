/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps Between Right Resolutions of Different Objects

A morphism between right resolutions over different target objects consists of a morphism
between the resolving models together with its comparison square.  This is the neutral input for
functorial constructions on chosen right resolutions.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.RightResolution

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂}

/-- A map of right resolutions lying over a morphism between their target objects. -/
@[stacks 0GSL "map of right resolutions"]
structure Map {X Y : C₂} (f : X ⟶ Y)
    (R : Φ.RightResolution X) (S : Φ.RightResolution Y) where
  /-- The morphism between the resolving models. -/
  modelHom : R.model ⟶ S.model
  /-- Compatibility of the model morphism with the target morphism and comparisons. -/
  comparison_naturality : R.comparison ≫ Φ.functor.map modelHom = f ≫ S.comparison

attribute [reassoc] Map.comparison_naturality

namespace Map

variable {X Y Z T : C₂} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  {R : Φ.RightResolution X} {S : Φ.RightResolution Y}
  {U : Φ.RightResolution Z} {V : Φ.RightResolution T}

/-- The morphism between target-category models underlying a map of right resolutions. -/
abbrev hom (m : Map f R S) : Φ.functor.obj R.model ⟶ Φ.functor.obj S.model :=
  Φ.functor.map m.modelHom

/-- Maps of right resolutions are determined by their morphisms between resolving models. -/
@[ext]
theorem ext {m n : Map f R S} (h : m.modelHom = n.modelHom) : m = n := by
  cases m
  cases n
  cases h
  rfl

/-- The identity model morphism satisfies the right-resolution comparison square. -/
theorem id_naturality (R : Φ.RightResolution X) :
    R.comparison ≫ Φ.functor.map (𝟙 R.model) = (𝟙 X) ≫ R.comparison := by
  simp

/-- The identity map of a right resolution. -/
@[stacks 0GSL "identity map of right resolutions"]
def id (R : Φ.RightResolution X) : Map (𝟙 X) R R where
  modelHom := 𝟙 R.model
  comparison_naturality := id_naturality R

/-- The identity right-resolution map has identity model morphism. -/
@[simp]
theorem id_modelHom (R : Φ.RightResolution X) : (id R).modelHom = 𝟙 R.model := by
  rfl

/-- The identity right-resolution map has identity target-model morphism. -/
@[simp]
theorem id_hom (R : Φ.RightResolution X) :
    (id R).hom = 𝟙 (Φ.functor.obj R.model) := by
  simp [hom]

/-- Composite model morphisms satisfy the comparison square for the composite target map. -/
theorem comp_naturality (m : Map f R S) (n : Map g S U) :
    R.comparison ≫ Φ.functor.map (m.modelHom ≫ n.modelHom) =
      (f ≫ g) ≫ U.comparison := by
  simp only [Φ.functor.map_comp, Category.assoc]
  rw [m.comparison_naturality_assoc, n.comparison_naturality]

/-- Compose maps of right resolutions. -/
@[stacks 0GSL "composition of maps of right resolutions"]
def comp (m : Map f R S) (n : Map g S U) : Map (f ≫ g) R U where
  modelHom := m.modelHom ≫ n.modelHom
  comparison_naturality := comp_naturality m n

/-- Composition of right-resolution maps composes their model morphisms. -/
@[simp]
theorem comp_modelHom (m : Map f R S) (n : Map g S U) :
    (comp m n).modelHom = m.modelHom ≫ n.modelHom := by
  rfl

/-- Composition of right-resolution maps composes their target-model morphisms. -/
@[simp]
theorem comp_hom (m : Map f R S) (n : Map g S U) :
    (comp m n).hom = m.hom ≫ n.hom := by
  simp [hom]

/-- Reindexing along an equality of target morphisms preserves the comparison square. -/
theorem reindex_naturality {f' : X ⟶ Y} (e : f = f') (m : Map f R S) :
    R.comparison ≫ Φ.functor.map m.modelHom = f' ≫ S.comparison := by
  subst f'
  exact m.comparison_naturality

/-- Reindex a map of right resolutions along an equality of target morphisms. -/
@[stacks 0GSL "reindexing maps of right resolutions"]
def reindex {f' : X ⟶ Y} (e : f = f') (m : Map f R S) : Map f' R S where
  modelHom := m.modelHom
  comparison_naturality := reindex_naturality e m

/-- Reindexing a right-resolution map retains its model morphism. -/
@[simp]
theorem reindex_modelHom {f' : X ⟶ Y} (e : f = f') (m : Map f R S) :
    (reindex e m).modelHom = m.modelHom := by
  rfl

/-- Reindexing a right-resolution map retains its target-model morphism. -/
@[simp]
theorem reindex_hom {f' : X ⟶ Y} (e : f = f') (m : Map f R S) :
    (reindex e m).hom = m.hom := by
  rfl

/-- Reindexing along reflexivity leaves a right-resolution map unchanged. -/
@[simp]
theorem reindex_rfl (m : Map f R S) : reindex rfl m = m := by
  apply ext
  rfl

/-- Successive reindexings of a right-resolution map combine by transitivity. -/
@[simp]
theorem reindex_trans {f' f'' : X ⟶ Y} (e : f = f') (e' : f' = f'')
    (m : Map f R S) :
    reindex e' (reindex e m) = reindex (e.trans e') m := by
  apply ext
  rfl

/-- Reindexing a right-resolution map along an equality and then its inverse recovers the map. -/
@[simp]
theorem reindex_symm {f' : X ⟶ Y} (e : f = f') (m : Map f R S) :
    reindex e.symm (reindex e m) = m := by
  apply ext
  rfl

/-- Reindexing the left target morphism of a composite agrees with first reindexing its left
factor. -/
@[simp]
theorem reindex_comp_left {f' : X ⟶ Y} (e : f = f')
    (m : Map f R S) (n : Map g S U) :
    reindex (congrArg (fun k : X ⟶ Y => k ≫ g) e) (comp m n) =
      comp (reindex e m) n := by
  apply ext
  rfl

/-- Reindexing the right target morphism of a composite agrees with first reindexing its right
factor. -/
@[simp]
theorem reindex_comp_right {g' : Y ⟶ Z} (e : g = g')
    (m : Map f R S) (n : Map g S U) :
    reindex (congrArg (fun k : Y ⟶ Z => f ≫ k) e) (comp m n) =
      comp m (reindex e n) := by
  apply ext
  rfl

/-- Reindexing both target morphisms of a composite commutes with composition. -/
@[simp]
theorem reindex_comp {f' : X ⟶ Y} {g' : Y ⟶ Z}
    (e : f = f') (e' : g = g') (m : Map f R S) (n : Map g S U) :
    reindex (congrArg₂ (fun (a : X ⟶ Y) (b : Y ⟶ Z) => a ≫ b) e e')
        (comp m n) =
      comp (reindex e m) (reindex e' n) := by
  apply ext
  rfl

/-- The comparison square of a same-target resolution morphism gives a resolution map over the
identity. -/
theorem ofHom_naturality {R S : Φ.RightResolution X} (m : R ⟶ S) :
    R.comparison ≫ Φ.functor.map (RightResolution.modelHom m) =
      (𝟙 X) ≫ S.comparison := by
  simpa using m.comm

/-- Regard a morphism in the category of right resolutions as a map over the identity. -/
def ofHom {R S : Φ.RightResolution X} (m : R ⟶ S) : Map (𝟙 X) R S where
  modelHom := RightResolution.modelHom m
  comparison_naturality := ofHom_naturality m

/-- `ofHom` retains the morphism between resolving models. -/
@[simp]
theorem ofHom_modelHom {R S : Φ.RightResolution X} (m : R ⟶ S) :
    (ofHom m).modelHom = RightResolution.modelHom m := by
  rfl

/-- `ofHom` retains the target-model morphism. -/
@[simp]
theorem ofHom_hom {R S : Φ.RightResolution X} (m : R ⟶ S) :
    (ofHom m).hom = RightResolution.hom m := by
  rfl

/-- `ofHom` sends the identity resolution morphism to the identity resolution map. -/
@[simp]
theorem ofHom_id (R : Φ.RightResolution X) : ofHom (𝟙 R) = id R := by
  apply ext
  rfl

/-- `ofHom` preserves composition after identifying the composite base identity with the
identity. -/
@[simp]
theorem ofHom_comp {R S U : Φ.RightResolution X} (m : R ⟶ S) (n : S ⟶ U) :
    reindex (Category.id_comp (𝟙 X)) (comp (ofHom m) (ofHom n)) =
      ofHom (m ≫ n) := by
  apply ext
  rfl

/-- The comparison square of a map over the identity defines a morphism in the category of
right resolutions. -/
theorem toHom_comm {R S : Φ.RightResolution X} (m : Map (𝟙 X) R S) :
    R.comparison ≫ Φ.functor.map m.modelHom = S.comparison := by
  simpa using m.comparison_naturality

/-- Regard a right-resolution map over the identity as a morphism in the resolution category. -/
def toHom {R S : Φ.RightResolution X} (m : Map (𝟙 X) R S) : R ⟶ S where
  f := m.modelHom
  comm := toHom_comm m

/-- `toHom` retains the morphism between resolving models. -/
@[simp]
theorem toHom_modelHom {R S : Φ.RightResolution X} (m : Map (𝟙 X) R S) :
    RightResolution.modelHom (toHom m) = m.modelHom := by
  rfl

/-- `toHom` retains the target-model morphism. -/
@[simp]
theorem toHom_hom {R S : Φ.RightResolution X} (m : Map (𝟙 X) R S) :
    RightResolution.hom (toHom m) = m.hom := by
  rfl

/-- `toHom` sends the identity resolution map to the identity resolution morphism. -/
@[simp]
theorem toHom_id (R : Φ.RightResolution X) : toHom (id R) = 𝟙 R := by
  apply RightResolution.hom_ext
  rfl

/-- `toHom` preserves composition after identifying the composite base identity with the
identity. -/
@[simp]
theorem toHom_comp {R S U : Φ.RightResolution X}
    (m : Map (𝟙 X) R S) (n : Map (𝟙 X) S U) :
    toHom (reindex (Category.id_comp (𝟙 X)) (comp m n)) = toHom m ≫ toHom n := by
  apply RightResolution.hom_ext
  rfl

/-- Passing a resolution morphism through `ofHom` and `toHom` returns it. -/
@[simp]
theorem toHom_ofHom {R S : Φ.RightResolution X} (m : R ⟶ S) :
    toHom (ofHom m) = m := by
  apply RightResolution.hom_ext
  rfl

/-- Passing a resolution map over the identity through `toHom` and `ofHom` returns it. -/
@[simp]
theorem ofHom_toHom {R S : Φ.RightResolution X} (m : Map (𝟙 X) R S) :
    ofHom (toHom m) = m := by
  apply ext
  rfl

/-- Morphisms in one fiber of right resolutions are equivalent to resolution maps over the
identity target morphism. -/
@[stacks 0GSL "fiber morphisms as right-resolution maps"]
def homEquiv {R S : Φ.RightResolution X} : (R ⟶ S) ≃ Map (𝟙 X) R S where
  toFun := ofHom
  invFun := toHom
  left_inv := toHom_ofHom
  right_inv := ofHom_toHom

/-- The identity law for composition of right-resolution maps. -/
@[simp]
theorem id_comp (m : Map f R S) :
    reindex (Category.id_comp f) (comp (id R) m) = m := by
  apply ext
  simp

/-- The right identity law for composition of right-resolution maps. -/
@[simp]
theorem comp_id (m : Map f R S) :
    reindex (Category.comp_id f) (comp m (id S)) = m := by
  apply ext
  simp

/-- Associativity of composition of right-resolution maps, after reindexing the target map. -/
theorem assoc (m : Map f R S) (n : Map g S U) (k : Map h U V) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := by
  apply ext
  simp [Category.assoc]

end Map

end CategoryTheory.LocalizerMorphism.RightResolution


