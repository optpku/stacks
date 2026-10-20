/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Category.TopCat.Subset

/-!
# Stable subspace diagrams

This module constructs the diagram of subspaces defined by a family of subsets preserved by the
transition maps of a `TopCat`-valued functor.
-/

@[expose] public section

open CategoryTheory Set TopologicalSpace

universe u v w

namespace CategoryTheory.Functor

variable {I : Type v} [Category.{w} I]
variable {F : I ⥤ TopCat.{max u v}}
variable (Z : ∀ i, Set (F.obj i))
variable (hZ : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))

/-- The morphism on subspaces induced by a transition map preserving a chosen family of subsets. -/
def stableSubsetDiagramMap {i j : I} (a : i ⟶ j) :
    TopCat.of (Z i) ⟶ TopCat.of (Z j) :=
  TopCat.ofHom
    ⟨Set.MapsTo.restrict (F.map a) (Z i) (Z j) (hZ a),
      Continuous.restrict (hZ a) (F.map a).hom.continuous⟩

/-- A restricted transition map has the same ambient value as the original transition map. -/
@[simp]
theorem stableSubsetDiagramMap_apply {i j : I} (a : i ⟶ j) (x : Z i) :
    (stableSubsetDiagramMap Z hZ a x).1 = F.map a x.1 := sorry

/-- Restricting an identity transition map gives the identity on the selected subspace. -/
theorem stableSubsetDiagramMap_id (i : I) :
    stableSubsetDiagramMap Z hZ (𝟙 i) = 𝟙 (TopCat.of (Z i)) := sorry

/-- Restriction commutes with composition of transition maps. -/
theorem stableSubsetDiagramMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    stableSubsetDiagramMap Z hZ (a ≫ b) =
      stableSubsetDiagramMap Z hZ a ≫ stableSubsetDiagramMap Z hZ b := sorry

/-- The diagram of subspaces defined by a transition-stable family of subsets. -/
@[stacks 0A2V "stable subset diagram"]
def stableSubsetDiagram : I ⥤ TopCat.{max u v} where
  obj i := TopCat.of (Z i)
  map a := stableSubsetDiagramMap Z hZ a
  map_id i := stableSubsetDiagramMap_id Z hZ i
  map_comp a b := stableSubsetDiagramMap_comp Z hZ a b

/-- The object at `i` of a stable-subset diagram is the selected subspace. -/
@[simp]
theorem stableSubsetDiagram_obj (i : I) :
    (stableSubsetDiagram Z hZ).obj i = TopCat.of (Z i) := sorry

/-- The map at `a` of a stable-subset diagram is the restricted ambient map. -/
@[simp]
theorem stableSubsetDiagram_map {i j : I} (a : i ⟶ j) :
    (stableSubsetDiagram Z hZ).map a = stableSubsetDiagramMap Z hZ a := sorry

/-- The natural transformation which includes a stable-subset diagram into its ambient diagram. -/
@[stacks 0A2V "stable subset diagram inclusion"]
def stableSubsetDiagramInclusion : F.stableSubsetDiagram Z hZ ⟶ F where
  app i := TopCat.subsetInclusion (Z i)
  naturality _ := sorry

/-- The component of the stable-subset inclusion is the canonical subtype inclusion. -/
@[simp]
theorem stableSubsetDiagramInclusion_app (i : I) :
    (stableSubsetDiagramInclusion Z hZ).app i = TopCat.subsetInclusion (Z i) := sorry

/-- The stable-subset inclusion sends a subtype point to its ambient value. -/
@[simp]
theorem stableSubsetDiagramInclusion_app_apply (i : I) (x : Z i) :
    (stableSubsetDiagramInclusion Z hZ).app i x = x.1 := sorry

/-- The stable-subset inclusion commutes with every transition map. -/
@[reassoc]
theorem stableSubsetDiagramInclusion_naturality {i j : I} (a : i ⟶ j) :
    stableSubsetDiagramMap Z hZ a ≫ TopCat.subsetInclusion (Z j) =
      TopCat.subsetInclusion (Z i) ≫ F.map a := sorry

end CategoryTheory.Functor
