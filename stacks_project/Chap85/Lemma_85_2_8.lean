/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Simplicial.Augmentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject CategoryTheory.Limits
open TopologicalSpace Opposite
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

universe u

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

/- Lemma 85.2.8: an augmentation induces a canonical morphism of sheaf topoi. -/
@[stacks 09W4] #check (CategoryTheory.SimplicialObject.augmentationMorphism a :
  MorphismOfTopoiIn (Opens.grothendieckTopology X) (zariskiTopology Y))

/- Lemma 85.2.8 (1): inverse image restricts to degreewise topological inverse image. -/
@[stacks 09W4] #check (CategoryTheory.SimplicialObject.inverseImage_component a :
  ∀ (n : ℕ) (F : Sheaf (Opens.grothendieckTopology X) (Type u)),
    (sheafComponent Y n (Type u)).obj ((augmentationMorphism a)⁻¹.obj F) ≅
      (componentTopos a n)⁻¹.obj F)

/- Lemma 85.2.8 (2): augmentation maps commute with the simplicial structure maps. -/
@[stacks 09W4] #check (CategoryTheory.SimplicialObject.component_naturality a :
  ∀ {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌),
    Y.map φ.op ≫ componentSpaceMap a m = componentSpaceMap a n)

/- Lemma 85.2.8 (3): the composite with a component morphism is the component map. -/
@[stacks 09W4] #check (CategoryTheory.SimplicialObject.comp_component a :
  ∀ (n : ℕ), (augmentationMorphism a)⁻¹ ⋙ (componentMorphism Y n)⁻¹ ≅
    (componentTopos a n)⁻¹)

/- Lemma 85.2.8 (4): direct image is the equalizer of the two coface-induced maps. -/
@[stacks 09W4] #check (CategoryTheory.SimplicialObject.Augmentation.pushforwardFork_isLimit a :
  ∀ (G : Sheaf (zariskiTopology Y) (Type u)), IsLimit (Augmentation.pushforwardFork a G))
