/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.FaceFamily
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degeneracy face families

A top-dimensional degeneracy is determined by its face coordinates.  This file constructs that
explicit compatible family directly, using the simplicial composite `δ_i ≫ σ_j` in each
coordinate.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial SimplexCategory.Truncated

universe u v

namespace CategoryTheory.SimplicialObject.Truncated.matching.FaceFamily

variable {C : Type u} [Category.{v} C]

namespace Compatible

/-- The coordinates induced by `δ_i ≫ σ_j` satisfy the matching-face compatibility
relations. -/
@[stacks 0188 "degeneracy face compatibility"]
theorem degeneracy {n : ℕ} (U : SimplicialObject.Truncated C n) {T : C}
    (j : Fin (n + 1))
    (f : T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) :
    FaceFamily.Compatible U
      (fun i ↦ f ≫ U.map
        (SimplexCategory.Truncated.Hom.tr
          (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op) := sorry

end Compatible

/-- The compatible face family induced by the `j`-th degeneracy of a map into the current top
degree.  Its `i`-th coordinate is indexed by the composite `δ_i ≫ σ_j`. -/
@[stacks 0188 "matching degeneracy face family"]
def degeneracy {n : ℕ} (U : SimplicialObject.Truncated C n) {T : C}
    (j : Fin (n + 1))
    (f : T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) : FaceFamily U T where
  app i := f ≫ U.map
    (SimplexCategory.Truncated.Hom.tr
      (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op
  compatible := Compatible.degeneracy U j f

/-- The `i`-th coordinate of a degeneracy face family is the textbook composite
`f ≫ U.map (δ_i ≫ σ_j)`. -/
@[simp, reassoc, stacks 0188 "matching degeneracy face coordinate"]
theorem degeneracy_app {n : ℕ} (U : SimplicialObject.Truncated C n) {T : C}
    (i : Fin (n + 2)) (j : Fin (n + 1))
    (f : T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) :
    (degeneracy U j f).app i =
      f ≫ U.map
        (SimplexCategory.Truncated.Hom.tr
          (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op := sorry

/-- In degree zero, both coordinates of the unique degeneracy face family are the original
map. -/
@[stacks 0188 "zero-degree matching degeneracy face family"]
theorem degeneracy_zero (U : SimplicialObject.Truncated C 0) {T : C}
    (f : T ⟶ U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))) :
    (fun i : Fin 2 ↦ (degeneracy U 0 f).app i) = fun _ : Fin 2 ↦ f := sorry

end CategoryTheory.SimplicialObject.Truncated.matching.FaceFamily
