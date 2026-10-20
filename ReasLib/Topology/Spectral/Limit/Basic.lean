/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Category.TopCat.StableSubset

/-!
# Basic inverse-limit results for spectral spaces

This module provides compactness and nonemptiness results for diagrams of spectral spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v w

noncomputable section

variable {I : Type v} [Category.{w} I]
variable {F : I ⥤ TopCat.{max u v}}
variable [∀ i, SpectralSpace (F.obj i)]

/-- A limit of constructibly closed, transition-stable subspaces of a spectral diagram is compact. -/
@[stacks 0A2V "stable constructibly closed subsets"]
theorem compactSpace_limit_of_constructibleClosed_stableSubsetDiagram
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    CompactSpace (limit (F.stableSubsetDiagram Z hZ_maps) : TopCat) := sorry

/-- The limit of a spectral diagram with spectral transition maps is compact. -/
@[stacks 0A2V "spectral inverse limits are compact"]
theorem compactSpace_limit_of_spectralSpaceDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a)) :
    CompactSpace (limit F : TopCat) := sorry

section

variable [IsCofiltered I]

/-- A cofiltered limit of nonempty constructibly closed, transition-stable subspaces of spectral
spaces is nonempty. -/
@[stacks 0A2W "stable nonempty constructibly closed subsets"]
theorem nonempty_limit_of_constructibleClosed_stableSubsetDiagram
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_nonempty : ∀ i, (Z i).Nonempty)
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    Nonempty (limit (F.stableSubsetDiagram Z hZ_maps) : TopCat) := sorry

/-- A cofiltered limit of nonempty spectral spaces with spectral transition maps is nonempty. -/
@[stacks 0A2W "nonempty spectral inverse limits"]
theorem nonempty_limit_of_spectralSpaceDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    [∀ i : I, Nonempty (F.obj i)] :
    Nonempty (limit F : TopCat) := sorry

end
