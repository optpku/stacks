/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Ext

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ENat

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- For a Noetherian local ring with a normalized dualizing complex, the ring depth is
the least natural degree with nonzero cohomology in the corresponding negative degree. -/
theorem depth_eq_least_nonzero_cohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (s : ModuleCat.single0 (ModuleCat.of A A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H) :
    ∃ δ : ℕ, moduleDepth A A = (δ : ℕ∞) ∧
      IsLeast
        {d : ℕ | ¬ IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj ω)}
        δ := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
