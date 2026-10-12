/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Right
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of Right Resolutions by an Object Property

This file specializes maps of localizer-morphism right resolutions to models in a full
subcategory.  The model morphism stays bundled, while `Map.hom` exposes its ambient image.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty.RightResolution

variable {D : Type u} [Category.{v} D]
  {P : ObjectProperty D} {S : MorphismProperty D}

/-- A map between property-indexed right resolutions over a morphism of target objects. -/
@[stacks 0GSL "map of property-indexed right resolutions"]
abbrev Map {X Y : D} (f : X ⟶ Y)
    (R : RightResolution P S X) (R' : RightResolution P S Y) :=
  LocalizerMorphism.RightResolution.Map f R R'

namespace Map

variable {X Y Z T : D} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  {R : RightResolution P S X} {R' : RightResolution P S Y}
  {R'' : RightResolution P S Z} {R''' : RightResolution P S T}

/-- Construct a map of property-indexed right resolutions from a morphism of bundled models
and its comparison square. -/
def mk (modelHom : R.model ⟶ R'.model)
    (comparison_naturality :
      R.comparison ≫ P.ι.map modelHom = f ≫ R'.comparison) : Map f R R' :=
  LocalizerMorphism.RightResolution.Map.mk modelHom comparison_naturality

/-- The bundled model morphism underlying a map of property-indexed right resolutions. -/
abbrev modelHom (m : Map f R R') : R.model ⟶ R'.model :=
  LocalizerMorphism.RightResolution.Map.modelHom m

/-- The ambient morphism underlying a map of property-indexed right resolutions. -/
abbrev hom (m : Map f R R') : R.object ⟶ R'.object :=
  LocalizerMorphism.RightResolution.Map.hom m

/-- The constructor for maps of property-indexed right resolutions retains its bundled model
morphism. -/
@[simp]
theorem mk_modelHom (modelHom : R.model ⟶ R'.model)
    (comparison_naturality :
      R.comparison ≫ P.ι.map modelHom = f ≫ R'.comparison) :
    (mk modelHom comparison_naturality).modelHom = modelHom := sorry

/-- The ambient morphism of a constructed map is the image of its bundled model morphism. -/
@[simp]
theorem mk_hom (modelHom : R.model ⟶ R'.model)
    (comparison_naturality :
      R.comparison ≫ P.ι.map modelHom = f ≫ R'.comparison) :
    (mk modelHom comparison_naturality).hom = P.ι.map modelHom := sorry

/-- Maps of property-indexed right resolutions are determined by their bundled model
morphisms. -/
@[ext]
theorem ext {m n : Map f R R'} (h : m.modelHom = n.modelHom) : m = n := sorry

/-- A map of property-indexed right resolutions commutes with the comparisons in the ambient
category. -/
@[reassoc]
theorem comparison_naturality (m : Map f R R') :
    R.comparison ≫ m.hom = f ≫ R'.comparison := sorry

/-- The identity map of a property-indexed right resolution. -/
abbrev id (R : RightResolution P S X) : Map (𝟙 X) R R :=
  LocalizerMorphism.RightResolution.Map.id R

/-- The identity map has identity bundled model morphism. -/
@[simp]
theorem id_modelHom (R : RightResolution P S X) :
    (id R).modelHom = 𝟙 R.model := sorry

/-- The identity map has identity ambient morphism. -/
@[simp]
theorem id_hom (R : RightResolution P S X) :
    (id R).hom = 𝟙 R.object := sorry

/-- Compose maps of property-indexed right resolutions. -/
abbrev comp (m : Map f R R') (n : Map g R' R'') : Map (f ≫ g) R R'' :=
  LocalizerMorphism.RightResolution.Map.comp m n

/-- Composition of maps composes their bundled model morphisms. -/
@[simp]
theorem comp_modelHom (m : Map f R R') (n : Map g R' R'') :
    (comp m n).modelHom = m.modelHom ≫ n.modelHom := sorry

/-- Composition of maps composes their ambient morphisms. -/
@[simp]
theorem comp_hom (m : Map f R R') (n : Map g R' R'') :
    (comp m n).hom = m.hom ≫ n.hom := sorry

/-- Reindex a map of property-indexed right resolutions along an equality of target maps. -/
abbrev reindex {f' : X ⟶ Y} (e : f = f') (m : Map f R R') : Map f' R R' :=
  LocalizerMorphism.RightResolution.Map.reindex e m

/-- Reindexing a map retains its bundled model morphism. -/
@[simp]
theorem reindex_modelHom {f' : X ⟶ Y} (e : f = f') (m : Map f R R') :
    (reindex e m).modelHom = m.modelHom := sorry

/-- Reindexing a map retains its ambient morphism. -/
@[simp]
theorem reindex_hom {f' : X ⟶ Y} (e : f = f') (m : Map f R R') :
    (reindex e m).hom = m.hom := sorry

/-- Reindexing along reflexivity leaves a property-indexed right-resolution map unchanged. -/
@[simp]
theorem reindex_rfl (m : Map f R R') : reindex rfl m = m := sorry

/-- Successive reindexings of a property-indexed right-resolution map combine by transitivity. -/
@[simp]
theorem reindex_trans {f' f'' : X ⟶ Y} (e : f = f') (e' : f' = f'')
    (m : Map f R R') :
    reindex e' (reindex e m) = reindex (e.trans e') m := sorry

/-- Reindexing a property-indexed right-resolution map along an equality and its inverse
recovers the original map. -/
@[simp]
theorem reindex_symm {f' : X ⟶ Y} (e : f = f') (m : Map f R R') :
    reindex e.symm (reindex e m) = m := sorry

/-- Reindexing the left target morphism of a composite property-indexed right-resolution map
agrees with reindexing its left factor first. -/
@[simp]
theorem reindex_comp_left {f' : X ⟶ Y} (e : f = f')
    (m : Map f R R') (n : Map g R' R'') :
    reindex (congrArg (fun k : X ⟶ Y => k ≫ g) e) (comp m n) =
      comp (reindex e m) n := sorry

/-- Reindexing the right target morphism of a composite property-indexed right-resolution map
agrees with reindexing its right factor first. -/
@[simp]
theorem reindex_comp_right {g' : Y ⟶ Z} (e : g = g')
    (m : Map f R R') (n : Map g R' R'') :
    reindex (congrArg (fun k : Y ⟶ Z => f ≫ k) e) (comp m n) =
      comp m (reindex e n) := sorry

/-- Reindexing both target morphisms of a composite property-indexed right-resolution map
commutes with composition. -/
@[simp]
theorem reindex_comp {f' : X ⟶ Y} {g' : Y ⟶ Z}
    (e : f = f') (e' : g = g') (m : Map f R R') (n : Map g R' R'') :
    reindex (congrArg₂ (fun (a : X ⟶ Y) (b : Y ⟶ Z) => a ≫ b) e e')
        (comp m n) =
      comp (reindex e m) (reindex e' n) := sorry

/-- Regard a morphism in one right-resolution fiber as a map over the identity. -/
abbrev ofHom {R R' : RightResolution P S X} (m : R ⟶ R') : Map (𝟙 X) R R' :=
  LocalizerMorphism.RightResolution.Map.ofHom m

/-- `ofHom` retains the bundled model morphism of a property-indexed right-resolution
morphism. -/
@[simp]
theorem ofHom_modelHom {R R' : RightResolution P S X} (m : R ⟶ R') :
    (ofHom m).modelHom = RightResolution.modelHom m := sorry

/-- `ofHom` retains the ambient morphism of a property-indexed right-resolution morphism. -/
@[simp]
theorem ofHom_hom {R R' : RightResolution P S X} (m : R ⟶ R') :
    (ofHom m).hom = RightResolution.hom m := sorry

/-- `ofHom` sends the identity morphism in a property-indexed right-resolution fiber to the
identity resolution map. -/
@[simp]
theorem ofHom_id (R : RightResolution P S X) : ofHom (𝟙 R) = id R := sorry

/-- `ofHom` sends composition in a property-indexed right-resolution fiber to composition of
resolution maps, reindexed over the identity. -/
@[simp]
theorem ofHom_comp {R R' R'' : RightResolution P S X} (m : R ⟶ R') (n : R' ⟶ R'') :
    reindex (Category.id_comp (𝟙 X)) (comp (ofHom m) (ofHom n)) =
      ofHom (m ≫ n) := sorry

/-- Regard a map over the identity as a morphism in one right-resolution fiber. -/
abbrev toHom {R R' : RightResolution P S X} (m : Map (𝟙 X) R R') : R ⟶ R' :=
  LocalizerMorphism.RightResolution.Map.toHom m

/-- `toHom` retains the bundled model morphism of a property-indexed right-resolution map. -/
@[simp]
theorem toHom_modelHom {R R' : RightResolution P S X} (m : Map (𝟙 X) R R') :
    RightResolution.modelHom (toHom m) = m.modelHom := sorry

/-- `toHom` retains the ambient morphism of a property-indexed right-resolution map. -/
@[simp]
theorem toHom_hom {R R' : RightResolution P S X} (m : Map (𝟙 X) R R') :
    RightResolution.hom (toHom m) = m.hom := sorry

/-- `toHom` sends the identity property-indexed right-resolution map to the identity morphism in
its fiber. -/
@[simp]
theorem toHom_id (R : RightResolution P S X) : toHom (id R) = 𝟙 R := sorry

/-- `toHom` sends reindexed composition of property-indexed right-resolution maps over an
identity to composition in the resolution fiber. -/
@[simp]
theorem toHom_comp {R R' R'' : RightResolution P S X}
    (m : Map (𝟙 X) R R') (n : Map (𝟙 X) R' R'') :
    toHom (reindex (Category.id_comp (𝟙 X)) (comp m n)) = toHom m ≫ toHom n := sorry

/-- Passing a property-indexed right-resolution morphism through `ofHom` and `toHom` returns
the original morphism. -/
@[simp]
theorem toHom_ofHom {R R' : RightResolution P S X} (m : R ⟶ R') :
    toHom (ofHom m) = m := sorry

/-- Passing a property-indexed right-resolution map over an identity through `toHom` and
`ofHom` returns the original map. -/
@[simp]
theorem ofHom_toHom {R R' : RightResolution P S X} (m : Map (𝟙 X) R R') :
    ofHom (toHom m) = m := sorry

/-- Morphisms in one right-resolution fiber are equivalent to maps over the identity. -/
abbrev homEquiv {R R' : RightResolution P S X} : (R ⟶ R') ≃ Map (𝟙 X) R R' :=
  LocalizerMorphism.RightResolution.Map.homEquiv

/-- The left identity law for composition of property-indexed right-resolution maps. -/
@[simp]
theorem id_comp (m : Map f R R') :
    reindex (Category.id_comp f) (comp (id R) m) = m := sorry

/-- The right identity law for composition of property-indexed right-resolution maps. -/
@[simp]
theorem comp_id (m : Map f R R') :
    reindex (Category.comp_id f) (comp m (id R')) = m := sorry

/-- Associativity of property-indexed right-resolution map composition after reindexing the
target morphism. -/
theorem assoc (m : Map f R R') (n : Map g R' R'') (k : Map h R'' R''') :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := sorry

end Map

end CategoryTheory.ObjectProperty.RightResolution
