/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence
public import ReasLib.CategoryTheory.ShortComplex.ShortExact
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Cohomological Delta-Functor Exact Windows

The exact window associated to a cohomological delta functor is natural in
maps of short exact complexes. Component formulas are exposed so clients do
not have to unfold `ComposableArrows.homMk₅`.
-/

open CategoryTheory.ComposableArrows

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor.exactWindow

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- Naturality of the first arrow of an exact window under a map of short
complexes. -/
theorem map_f (F : CohomologicalDeltaFunctor A B) {S T : ShortComplex A}
    (φ : S ⟶ T) (n : ℕ) :
    (F.F n).obj.map S.f ≫ (F.F n).obj.map φ.τ₂ =
      (F.F n).obj.map φ.τ₁ ≫ (F.F n).obj.map T.f := sorry

/-- Naturality of the second arrow of an exact window under a map of short
complexes. -/
theorem map_g (F : CohomologicalDeltaFunctor A B) {S T : ShortComplex A}
    (φ : S ⟶ T) (n : ℕ) :
    (F.F n).obj.map S.g ≫ (F.F n).obj.map φ.τ₃ =
      (F.F n).obj.map φ.τ₂ ≫ (F.F n).obj.map T.g := sorry

/-- A map of short exact complexes induces a map between their exact
windows. -/
@[stacks 010R "naturality map of cohomological exact windows"]
def map (F : CohomologicalDeltaFunctor A B) {S T : ShortComplex A}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    F.exactWindow hS n ⟶ F.exactWindow hT n :=
  ComposableArrows.homMk₅
    ((F.F n).obj.map φ.τ₁) ((F.F n).obj.map φ.τ₂) ((F.F n).obj.map φ.τ₃)
    ((F.F (n + 1)).obj.map φ.τ₁) ((F.F (n + 1)).obj.map φ.τ₂)
    ((F.F (n + 1)).obj.map φ.τ₃)
    (map_f F φ n) (map_g F φ n) (F.δ_naturality hS hT φ n).w.symm
    (map_f F φ (n + 1)) (map_g F φ (n + 1))

/-- The degree-`n` first component of the induced map of exact windows. -/
@[simp]
theorem map_app_zero (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    (map F hS hT φ n).app 0 = (F.F n).obj.map φ.τ₁ := sorry

/-- The degree-`n` middle component of the induced map of exact windows. -/
@[simp]
theorem map_app_one (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    (map F hS hT φ n).app 1 = (F.F n).obj.map φ.τ₂ := sorry

/-- The degree-`n` third component of the induced map of exact windows. -/
@[simp]
theorem map_app_two (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    (map F hS hT φ n).app 2 = (F.F n).obj.map φ.τ₃ := sorry

/-- The degree-`n + 1` first component of the induced map of exact windows. -/
@[simp]
theorem map_app_three (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    (map F hS hT φ n).app 3 = (F.F (n + 1)).obj.map φ.τ₁ := sorry

/-- The degree-`n + 1` middle component of the induced map of exact windows. -/
@[simp]
theorem map_app_four (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    (map F hS hT φ n).app 4 = (F.F (n + 1)).obj.map φ.τ₂ := sorry

/-- The degree-`n + 1` last component of the induced map of exact windows. -/
@[simp]
theorem map_app_five (F : CohomologicalDeltaFunctor A B)
    {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    (map F hS hT φ n).app 5 = (F.F (n + 1)).obj.map φ.τ₃ := sorry

/-- Identity maps of short exact complexes induce identity maps of exact
windows. -/
@[simp]
theorem map_id (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    map F hS hS (𝟙 S) n = 𝟙 (F.exactWindow hS n) := sorry

/-- Maps of exact windows preserve composition of maps of short exact
complexes. -/
@[simp]
theorem map_comp (F : CohomologicalDeltaFunctor A B)
    {S T U : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (hU : U.ShortExact) (φ : S ⟶ T) (ψ : T ⟶ U) (n : ℕ) :
    map F hS hU (φ ≫ ψ) n =
      map F hS hT φ n ≫ map F hT hU ψ n := sorry

end CategoryTheory.CohomologicalDeltaFunctor.exactWindow
