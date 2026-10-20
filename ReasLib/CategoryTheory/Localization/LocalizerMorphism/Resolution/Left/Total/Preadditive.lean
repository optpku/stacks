/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Map.Preadditive
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Total.Map
public import Mathlib.CategoryTheory.Preadditive.Comma

/-!
# Preadditive Total Categories of Left Resolutions

The comma-category presentation makes the total category preadditive without a custom instance.
This leaf records only the projection and dependent-map computations that downstream users need.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.LeftResolution

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Preadditive C₁] [Preadditive C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂} [Φ.functor.Additive]

namespace Total

/-- The zero total morphism has zero base component. -/
@[simp]
theorem zero_baseHom {R S : Total Φ} : baseHom (0 : R ⟶ S) = 0 := sorry

/-- The zero total morphism has zero model component. -/
@[simp]
theorem zero_modelHom {R S : Total Φ} : modelHom (0 : R ⟶ S) = 0 := sorry

/-- Addition of total morphisms adds their base components. -/
@[simp]
theorem add_baseHom {R S : Total Φ} (f g : R ⟶ S) :
    baseHom (f + g) = baseHom f + baseHom g := sorry

/-- Addition of total morphisms adds their model components. -/
@[simp]
theorem add_modelHom {R S : Total Φ} (f g : R ⟶ S) :
    modelHom (f + g) = modelHom f + modelHom g := sorry

/-- Negation of a total morphism negates its base component. -/
@[simp]
theorem neg_baseHom {R S : Total Φ} (f : R ⟶ S) :
    baseHom (-f) = -baseHom f := sorry

/-- Negation of a total morphism negates its model component. -/
@[simp]
theorem neg_modelHom {R S : Total Φ} (f : R ⟶ S) :
    modelHom (-f) = -modelHom f := sorry

/-- Subtraction of total morphisms subtracts their base components. -/
@[simp]
theorem sub_baseHom {R S : Total Φ} (f g : R ⟶ S) :
    baseHom (f - g) = baseHom f - baseHom g := sorry

/-- Subtraction of total morphisms subtracts their model components. -/
@[simp]
theorem sub_modelHom {R S : Total Φ} (f g : R ⟶ S) :
    modelHom (f - g) = modelHom f - modelHom g := sorry

/-- Extracting the dependent map of a zero total morphism gives the dependent zero map after
reindexing its base component. -/
@[simp]
theorem toMap_zero {R S : Total Φ} :
    Map.reindex zero_baseHom (toMap (0 : R ⟶ S)) =
      Map.zero R.toResolution S.toResolution := sorry

/-- Extracting the dependent map of a sum gives the sum of the extracted maps after reindexing
its base component. -/
@[simp]
theorem toMap_add {R S : Total Φ} (f g : R ⟶ S) :
    Map.reindex (add_baseHom f g) (toMap (f + g)) =
      Map.add (toMap f) (toMap g) := sorry

/-- Extracting the dependent map of a negated total morphism gives the negated extracted map
after reindexing its base component. -/
@[simp]
theorem toMap_neg {R S : Total Φ} (f : R ⟶ S) :
    Map.reindex (neg_baseHom f) (toMap (-f)) = Map.neg (toMap f) := sorry

/-- Extracting the dependent map of a difference gives the difference of the extracted maps
after reindexing its base component. -/
@[simp]
theorem toMap_sub {R S : Total Φ} (f g : R ⟶ S) :
    Map.reindex (sub_baseHom f g) (toMap (f - g)) =
      Map.sub (toMap f) (toMap g) := sorry

/-- The dependent zero map becomes the zero total morphism. -/
@[simp]
theorem ofMap_zero {R S : Total Φ} :
    ofMap (Map.zero R.toResolution S.toResolution) = (0 : R ⟶ S) := sorry

/-- Constructing total morphisms from dependent maps preserves addition. -/
@[simp]
theorem ofMap_add {R S : Total Φ} {f g : R.base ⟶ S.base}
    (m : Map f R.toResolution S.toResolution)
    (n : Map g R.toResolution S.toResolution) :
    ofMap (Map.add m n) = ofMap m + ofMap n := sorry

/-- Constructing total morphisms from dependent maps preserves negation. -/
@[simp]
theorem ofMap_neg {R S : Total Φ} {f : R.base ⟶ S.base}
    (m : Map f R.toResolution S.toResolution) :
    ofMap (Map.neg m) = -ofMap m := sorry

/-- Constructing total morphisms from dependent maps preserves subtraction. -/
@[simp]
theorem ofMap_sub {R S : Total Φ} {f g : R.base ⟶ S.base}
    (m : Map f R.toResolution S.toResolution)
    (n : Map g R.toResolution S.toResolution) :
    ofMap (Map.sub m n) = ofMap m - ofMap n := sorry

end Total

namespace Map

variable {X Y : C₂} {f g : X ⟶ Y}
  {R : Φ.LeftResolution X} {S : Φ.LeftResolution Y}

/-- The dependent zero map becomes the zero total morphism. -/
@[simp]
theorem toTotalHom_zero :
    (Map.zero R S).toTotalHom = 0 := sorry

/-- Addition of dependent maps becomes addition of total morphisms. -/
@[simp]
theorem toTotalHom_add (m : Map f R S) (n : Map g R S) :
    (Map.add m n).toTotalHom = m.toTotalHom + n.toTotalHom := sorry

/-- Negation of a dependent map becomes negation of its total morphism. -/
@[simp]
theorem toTotalHom_neg (m : Map f R S) :
    (Map.neg m).toTotalHom = -m.toTotalHom := sorry

/-- Subtraction of dependent maps becomes subtraction of total morphisms. -/
@[simp]
theorem toTotalHom_sub (m : Map f R S) (n : Map g R S) :
    (Map.sub m n).toTotalHom = m.toTotalHom - n.toTotalHom := sorry

end Map

#synth Preadditive (Total Φ)
#synth (Total.baseFunctor Φ).Additive
#synth (Total.modelFunctor Φ).Additive

end CategoryTheory.LocalizerMorphism.LeftResolution
