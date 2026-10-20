/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Depth

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ENat

universe u

/- Lemma 47.20.1 -/
@[stacks 0AWR] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.depth_eq_least_nonzero_cohomology :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (s : ModuleCat.single0 (ModuleCat.of A A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H),
      ∃ δ : ℕ, moduleDepth A A = (δ : ℕ∞) ∧
        IsLeast
          {d : ℕ | ¬ IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj ω)}
          δ)
