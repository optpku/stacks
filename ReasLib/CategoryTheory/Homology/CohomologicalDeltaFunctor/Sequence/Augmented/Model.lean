/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Augmented.Naturality
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Model.Computation
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Model Maps of Augmented Cohomological Windows

This leaf records the tail and component computations for the action of a
delta-functor morphism on the augmented low-degree exact window.
-/

open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
variable {F G : CohomologicalDeltaFunctor A B} (τ : F ⟶ G)
variable {S : ShortComplex A} (hS : S.ShortExact)

/-- Removing the initial zero component of an augmented model map recovers
the low-degree exact-window model map. -/
@[simp, stacks 015B "augmented model map after removing the initial zero"]
theorem modelMap_δ₀ :
    δ₀Functor.map (modelMap τ hS) = lowDegreeWindowMap τ hS := sorry

/-- The zero-object component of an augmented model map is the identity. -/
@[simp, stacks 015B "zero component of an augmented model map"]
theorem modelMap_app_zero :
    (modelMap τ hS).app 0 = 𝟙 (0 : B) := sorry

/-- The `F⁰(X₁)` component of an augmented model map. -/
@[simp, stacks 015B "first degree first object component of an augmented model map"]
theorem modelMap_app_one :
    (modelMap τ hS).app 1 = (τ.app 0).app S.X₁ := sorry

/-- The `F⁰(X₂)` component of an augmented model map. -/
@[simp, stacks 015B "first degree second object component of an augmented model map"]
theorem modelMap_app_two :
    (modelMap τ hS).app 2 = (τ.app 0).app S.X₂ := sorry

/-- The `F⁰(X₃)` component of an augmented model map. -/
@[simp, stacks 015B "first degree third object component of an augmented model map"]
theorem modelMap_app_three :
    (modelMap τ hS).app 3 = (τ.app 0).app S.X₃ := sorry

/-- The `F¹(X₁)` component of an augmented model map. -/
@[simp, stacks 015B "second degree first object component of an augmented model map"]
theorem modelMap_app_four :
    (modelMap τ hS).app 4 = (τ.app 1).app S.X₁ := sorry

/-- The `F¹(X₂)` component of an augmented model map. -/
@[simp, stacks 015B "second degree second object component of an augmented model map"]
theorem modelMap_app_five :
    (modelMap τ hS).app 5 = (τ.app 1).app S.X₂ := sorry

/-- The `F¹(X₃)` component of an augmented model map. -/
@[simp, stacks 015B "second degree third object component of an augmented model map"]
theorem modelMap_app_six :
    (modelMap τ hS).app 6 = (τ.app 1).app S.X₃ := sorry

end CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow
