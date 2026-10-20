/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmentation
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation.Zero
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0G5Q

# Maps from the zero simplex

The zero simplex is terminal in the simplex category.  Consequently a map into the zero simplex
determines a unique map from a constant simplicial object.  The named API here is deliberately
independent of any resolution or chapter-specific notation, and delegates its underlying
constant-diagram construction to `Limits.IsInitial.constTo`.
-/

@[expose] public section

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open SimplexCategory
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The canonical map from the constant simplicial object on `Z` to `X` induced by `f`. -/
@[stacks 0G5Q "augmentation section from degree zero"]
def fromZero (X : SimplicialObject C) {Z : C} (f : Z ⟶ X _⦋0⦌) :
    (const C).obj Z ⟶ X :=
  SimplexCategory.isTerminalZero.op.constTo f

/-- Every component of `fromZero` is the defining zero-simplex map followed by the unique
simplex operator to degree zero. -/
@[simp, stacks 0G5Q "augmentation section component formula"]
theorem fromZero.app (X : SimplicialObject C) {Z : C} (f : Z ⟶ X _⦋0⦌)
    (Δ : SimplexCategoryᵒᵖ) :
    (fromZero X f).app Δ =
      f ≫ X.map (SimplexCategory.isTerminalZero.from (unop Δ)).op := sorry

/-- The degree-zero component of `fromZero` is the map from which it was constructed. -/
@[simp, stacks 0G5Q "augmentation section degree-zero component"]
theorem fromZero.app.zero (X : SimplicialObject C) {Z : C} (f : Z ⟶ X _⦋0⦌) :
    (fromZero X f).app (op ⦋0⦌) = f := sorry

/-- Reconstructing a map from a constant simplicial object from its degree-zero component
recovers the original map. -/
@[stacks 0G5Q "constant-source map reconstruction"]
theorem fromZero.ofAppZero (X : SimplicialObject C) {Z : C}
    (f : (const C).obj Z ⟶ X) :
    fromZero X (f.app (op ⦋0⦌)) = f := sorry

/-- Maps from a constant simplicial object are determined by their degree-zero components. -/
@[ext, stacks 0G5Q "constant-source map extensionality"]
theorem fromZero.hom_ext (X : SimplicialObject C) {Z : C}
    (f g : (const C).obj Z ⟶ X)
    (h : f.app (op ⦋0⦌) = g.app (op ⦋0⦌)) :
    f = g := sorry

/-- Maps from the constant simplicial object on `Z` to `X` are equivalent to maps from `Z`
into the zero simplices of `X`. -/
@[stacks 0G5Q "constant-source map zero-simplex equivalence"]
def fromZero.homEquiv (X : SimplicialObject C) (Z : C) :
    ((const C).obj Z ⟶ X) ≃ (Z ⟶ X _⦋0⦌) :=
  evalZero.constHomEquiv Z X

/-- The forward map of `fromZero.homEquiv` is evaluation in degree zero. -/
@[simp, stacks 0G5Q "constant-source map equivalence forward formula"]
theorem fromZero.homEquiv.apply (X : SimplicialObject C) (Z : C)
    (f : (const C).obj Z ⟶ X) :
    fromZero.homEquiv X Z f = f.app (op ⦋0⦌) := sorry

/-- The inverse of `fromZero.homEquiv` is reconstruction by `fromZero`. -/
@[simp, stacks 0G5Q "constant-source map equivalence inverse formula"]
theorem fromZero.homEquiv.symm_apply (X : SimplicialObject C) (Z : C)
    (f : Z ⟶ X _⦋0⦌) :
    (fromZero.homEquiv X Z).symm f = fromZero X f := sorry

/-- A section at degree zero gives a section of an entire augmentation. -/
@[stacks 0G5Q "augmentation section property"]
theorem fromZero.comp_hom (X : SimplicialObject.Augmented C)
    (f : X.right ⟶ X.left _⦋0⦌)
    (hf : f ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right) :
    fromZero X.left f ≫ X.hom = 𝟙 _ := sorry

end CategoryTheory.SimplicialObject
