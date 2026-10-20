/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Category

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Augmented
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Naturality
public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp.Map
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Augmented Cohomological Windows

The standard low-degree sequence beginning at the zero object is natural in
maps of short exact complexes and in morphisms of cohomological delta
functors.  Both actions are obtained from functorial zero precomposition.
-/

open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]

/-- A map of short exact complexes induces a map between their augmented
low-degree cohomological windows. -/
@[stacks 010R "naturality map of augmented cohomological windows"]
def map (F : CohomologicalDeltaFunctor A B) {S T : ShortComplex A}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    F.augmentedWindow hS ⟶ F.augmentedWindow hT :=
  zeroPrecomp.map (exactWindow.map F hS hT φ 0) 1

/-- Removing the initial zero component recovers the low-degree
exact-window naturality map. -/
@[simp]
theorem map_δ₀ (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    δ₀Functor.map (map F hS hT φ) = exactWindow.map F hS hT φ 0 := sorry

/-- The zero-object component of an augmented-window map is the identity. -/
@[simp]
theorem map_app_zero (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    (map F hS hT φ).app 0 = 𝟙 (0 : B) := sorry

/-- The `F⁰(X₁)` component of an augmented-window map. -/
@[simp]
theorem map_app_one (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    (map F hS hT φ).app 1 = (F.F 0).obj.map φ.τ₁ := sorry

/-- The `F⁰(X₂)` component of an augmented-window map. -/
@[simp]
theorem map_app_two (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    (map F hS hT φ).app 2 = (F.F 0).obj.map φ.τ₂ := sorry

/-- The `F⁰(X₃)` component of an augmented-window map. -/
@[simp]
theorem map_app_three (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    (map F hS hT φ).app 3 = (F.F 0).obj.map φ.τ₃ := sorry

/-- The `F¹(X₁)` component of an augmented-window map. -/
@[simp]
theorem map_app_four (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    (map F hS hT φ).app 4 = (F.F 1).obj.map φ.τ₁ := sorry

/-- The `F¹(X₂)` component of an augmented-window map. -/
@[simp]
theorem map_app_five (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    (map F hS hT φ).app 5 = (F.F 1).obj.map φ.τ₂ := sorry

/-- The `F¹(X₃)` component of an augmented-window map. -/
@[simp]
theorem map_app_six (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    (map F hS hT φ).app 6 = (F.F 1).obj.map φ.τ₃ := sorry

/-- Augmented-window maps preserve identities of short exact complexes. -/
@[simp]
theorem map_id (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) :
    map F hS hS (𝟙 S) = 𝟙 (F.augmentedWindow hS) := sorry

/-- Augmented-window maps preserve composition of maps of short exact
complexes. -/
@[simp]
theorem map_comp (F : CohomologicalDeltaFunctor A B)
    {S T U : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (hU : U.ShortExact) (φ : S ⟶ T) (ψ : T ⟶ U) :
    map F hS hU (φ ≫ ψ) =
      map F hS hT φ ≫ map F hT hU ψ := sorry

/-- A morphism of cohomological delta functors induces a map between their
augmented low-degree windows. -/
@[stacks 010R "map of augmented windows between cohomological delta functors"]
def modelMap {F G : CohomologicalDeltaFunctor A B} (τ : F ⟶ G)
    {S : ShortComplex A} (hS : S.ShortExact) :
    F.augmentedWindow hS ⟶ G.augmentedWindow hS :=
  zeroPrecomp.map (lowDegreeWindowMap τ hS) 1

/-- Augmented model maps preserve identity morphisms. -/
@[simp]
theorem modelMap_id (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) :
    modelMap (𝟙 F) hS = 𝟙 (F.augmentedWindow hS) := sorry

/-- Augmented model maps preserve composition. -/
@[simp]
theorem modelMap_comp {F G H : CohomologicalDeltaFunctor A B}
    (τ : F ⟶ G) (σ : G ⟶ H) {S : ShortComplex A}
    (hS : S.ShortExact) :
    modelMap (τ ≫ σ) hS = modelMap τ hS ≫ modelMap σ hS := sorry

end CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow
