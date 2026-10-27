/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps Between Left Resolutions of Different Objects

A morphism between left resolutions over different target objects consists of a morphism between
the resolving models together with its comparison square.  This is the neutral input for
functorial constructions on chosen left resolutions.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.LeftResolution

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂}

/-- A map of left resolutions lying over a morphism between their target objects. -/
@[stacks 0GSL "map of left resolutions"]
structure Map {X Y : C₂} (f : X ⟶ Y)
    (R : Φ.LeftResolution X) (S : Φ.LeftResolution Y) where
  /-- The morphism between the resolving models. -/
  modelHom : R.model ⟶ S.model
  /-- Compatibility of the model morphism with the target morphism and comparisons. -/
  comparison_naturality : Φ.functor.map modelHom ≫ S.comparison = R.comparison ≫ f

attribute [reassoc] Map.comparison_naturality

namespace Map

variable {X Y Z T : C₂} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  {R : Φ.LeftResolution X} {S : Φ.LeftResolution Y}
  {U : Φ.LeftResolution Z} {V : Φ.LeftResolution T}

/-- The morphism between target-category models underlying a map of left resolutions. -/
abbrev hom (m : Map f R S) : Φ.functor.obj R.model ⟶ Φ.functor.obj S.model :=
  Φ.functor.map m.modelHom

/-- Maps of left resolutions are determined by their morphisms between resolving models. -/
@[ext]
theorem ext {m n : Map f R S} (h : m.modelHom = n.modelHom) : m = n := by
  cases m
  cases n
  cases h
  rfl

/-- The identity model morphism satisfies the left-resolution comparison square. -/
theorem id_naturality (R : Φ.LeftResolution X) :
    Φ.functor.map (𝟙 R.model) ≫ R.comparison = R.comparison ≫ 𝟙 X := by
  rw [Φ.functor.map_id, Category.id_comp, Category.comp_id]

/-- The identity map of a left resolution. -/
@[stacks 0GSL "identity map of left resolutions"]
def id (R : Φ.LeftResolution X) : Map (𝟙 X) R R where
  modelHom := 𝟙 R.model
  comparison_naturality := id_naturality R

/-- The identity left-resolution map has identity model morphism. -/
@[simp]
theorem id_modelHom (R : Φ.LeftResolution X) : (id R).modelHom = 𝟙 R.model := rfl

/-- The identity left-resolution map has identity target-model morphism. -/
@[simp]
theorem id_hom (R : Φ.LeftResolution X) :
    (id R).hom = 𝟙 (Φ.functor.obj R.model) := Φ.functor.map_id R.model

/-- Composite model morphisms satisfy the comparison square for the composite target map. -/
theorem comp_naturality (m : Map f R S) (n : Map g S U) :
    Φ.functor.map (m.modelHom ≫ n.modelHom) ≫ U.comparison =
      R.comparison ≫ (f ≫ g) := by
  rw [Φ.functor.map_comp, Category.assoc, n.comparison_naturality,
    m.comparison_naturality_assoc]

/-- Compose maps of left resolutions. -/
@[stacks 0GSL "composition of maps of left resolutions"]
def comp (m : Map f R S) (n : Map g S U) : Map (f ≫ g) R U where
  modelHom := m.modelHom ≫ n.modelHom
  comparison_naturality := comp_naturality m n

/-- Composition of left-resolution maps composes their model morphisms. -/
@[simp]
theorem comp_modelHom (m : Map f R S) (n : Map g S U) :
    (comp m n).modelHom = m.modelHom ≫ n.modelHom := rfl

/-- Composition of left-resolution maps composes their target-model morphisms. -/
@[simp]
theorem comp_hom (m : Map f R S) (n : Map g S U) :
    (comp m n).hom = m.hom ≫ n.hom := Φ.functor.map_comp m.modelHom n.modelHom

/-- Reindexing along an equality of target morphisms preserves the comparison square. -/
theorem reindex_naturality {f' : X ⟶ Y} (e : f = f') (m : Map f R S) :
    Φ.functor.map m.modelHom ≫ S.comparison = R.comparison ≫ f' := by
  exact m.comparison_naturality.trans (congrArg (fun k : X ⟶ Y => R.comparison ≫ k) e)

/-- Reindex a map of left resolutions along an equality of target morphisms. -/
@[stacks 0GSL "reindexing maps of left resolutions"]
def reindex {f' : X ⟶ Y} (e : f = f') (m : Map f R S) : Map f' R S where
  modelHom := m.modelHom
  comparison_naturality := reindex_naturality e m

/-- Reindexing a left-resolution map retains its model morphism. -/
@[simp]
theorem reindex_modelHom {f' : X ⟶ Y} (e : f = f') (m : Map f R S) :
    (reindex e m).modelHom = m.modelHom := rfl

/-- Reindexing a left-resolution map retains its target-model morphism. -/
@[simp]
theorem reindex_hom {f' : X ⟶ Y} (e : f = f') (m : Map f R S) :
    (reindex e m).hom = m.hom := rfl

/-- Reindexing along reflexivity leaves a left-resolution map unchanged. -/
@[simp]
theorem reindex_rfl (m : Map f R S) : reindex rfl m = m := by
  apply ext
  rfl

/-- Successive reindexings of a left-resolution map combine by transitivity. -/
@[simp]
theorem reindex_trans {f' f'' : X ⟶ Y} (e : f = f') (e' : f' = f'')
    (m : Map f R S) :
    reindex e' (reindex e m) = reindex (e.trans e') m := by
  apply ext
  rfl

/-- Reindexing a left-resolution map along an equality and then its inverse recovers the map. -/
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
theorem ofHom_naturality {R S : Φ.LeftResolution X} (m : R ⟶ S) :
    Φ.functor.map (LeftResolution.modelHom m) ≫ S.comparison =
      R.comparison ≫ 𝟙 X := by
  exact m.comm.trans (Category.comp_id R.comparison).symm

/-- Regard a morphism in the category of left resolutions as a map over the identity. -/
def ofHom {R S : Φ.LeftResolution X} (m : R ⟶ S) : Map (𝟙 X) R S where
  modelHom := LeftResolution.modelHom m
  comparison_naturality := ofHom_naturality m

/-- `ofHom` retains the morphism between resolving models. -/
@[simp]
theorem ofHom_modelHom {R S : Φ.LeftResolution X} (m : R ⟶ S) :
    (ofHom m).modelHom = LeftResolution.modelHom m := rfl

/-- `ofHom` retains the target-model morphism. -/
@[simp]
theorem ofHom_hom {R S : Φ.LeftResolution X} (m : R ⟶ S) :
    (ofHom m).hom = LeftResolution.hom m := rfl

/-- `ofHom` sends the identity resolution morphism to the identity resolution map. -/
@[simp]
theorem ofHom_id (R : Φ.LeftResolution X) : ofHom (𝟙 R) = id R := by
  apply ext
  rfl

/-- `ofHom` preserves composition after identifying the composite base identity with the
identity. -/
@[simp]
theorem ofHom_comp {R S U : Φ.LeftResolution X} (m : R ⟶ S) (n : S ⟶ U) :
    reindex (Category.id_comp (𝟙 X)) (comp (ofHom m) (ofHom n)) =
      ofHom (m ≫ n) := by
  apply ext
  rfl

/-- The comparison square of a map over the identity defines a morphism in the category of left
resolutions. -/
theorem toHom_comm {R S : Φ.LeftResolution X} (m : Map (𝟙 X) R S) :
    Φ.functor.map m.modelHom ≫ S.comparison = R.comparison := by
  simpa only [Category.comp_id] using m.comparison_naturality

/-- Regard a left-resolution map over the identity as a morphism in the resolution category. -/
def toHom {R S : Φ.LeftResolution X} (m : Map (𝟙 X) R S) : R ⟶ S where
  f := m.modelHom
  comm := toHom_comm m

/-- `toHom` retains the morphism between resolving models. -/
@[simp]
theorem toHom_modelHom {R S : Φ.LeftResolution X} (m : Map (𝟙 X) R S) :
    LeftResolution.modelHom (toHom m) = m.modelHom := rfl

/-- `toHom` retains the target-model morphism. -/
@[simp]
theorem toHom_hom {R S : Φ.LeftResolution X} (m : Map (𝟙 X) R S) :
    LeftResolution.hom (toHom m) = m.hom := rfl

/-- `toHom` sends the identity resolution map to the identity resolution morphism. -/
@[simp]
theorem toHom_id (R : Φ.LeftResolution X) : toHom (id R) = 𝟙 R := by
  apply LeftResolution.hom_ext
  rfl

/-- `toHom` preserves composition after identifying the composite base identity with the
identity. -/
@[simp]
theorem toHom_comp {R S U : Φ.LeftResolution X}
    (m : Map (𝟙 X) R S) (n : Map (𝟙 X) S U) :
    toHom (reindex (Category.id_comp (𝟙 X)) (comp m n)) = toHom m ≫ toHom n := by
  apply LeftResolution.hom_ext
  rfl

/-- Passing a resolution morphism through `ofHom` and `toHom` returns it. -/
@[simp]
theorem toHom_ofHom {R S : Φ.LeftResolution X} (m : R ⟶ S) :
    toHom (ofHom m) = m := by
  apply LeftResolution.hom_ext
  rfl

/-- Passing a resolution map over the identity through `toHom` and `ofHom` returns it. -/
@[simp]
theorem ofHom_toHom {R S : Φ.LeftResolution X} (m : Map (𝟙 X) R S) :
    ofHom (toHom m) = m := by
  apply ext
  rfl

/-- Morphisms in one fiber of left resolutions are equivalent to resolution maps over the
identity target morphism. -/
@[stacks 0GSL "fiber morphisms as left-resolution maps"]
def homEquiv {R S : Φ.LeftResolution X} : (R ⟶ S) ≃ Map (𝟙 X) R S where
  toFun := ofHom
  invFun := toHom
  left_inv := toHom_ofHom
  right_inv := ofHom_toHom

/-- The left identity law for composition of left-resolution maps. -/
@[simp]
theorem id_comp (m : Map f R S) :
    reindex (Category.id_comp f) (comp (id R) m) = m := by
  apply ext
  exact Category.id_comp m.modelHom

/-- The right identity law for composition of left-resolution maps. -/
@[simp]
theorem comp_id (m : Map f R S) :
    reindex (Category.comp_id f) (comp m (id S)) = m := by
  apply ext
  exact Category.comp_id m.modelHom

/-- Associativity of composition of left-resolution maps, after reindexing the target map. -/
theorem assoc (m : Map f R S) (n : Map g S U) (k : Map h U V) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := by
  apply ext
  exact Category.assoc m.modelHom n.modelHom k.modelHom

end Map

end CategoryTheory.LocalizerMorphism.LeftResolution


