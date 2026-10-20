/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

universe u

namespace PresheafOfModules

/-- A scalar-compatible, simplex-indexed homotopy between endomorphisms of a
presheaf of modules over a cosimplicial ring. -/
structure CosimplicialHomotopy
    {R : (SimplexCategoryᵒᵖ)ᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules R) (a b : M ⟶ M) where
  /-- The module map indexed by a simplex of the standard interval. -/
  hom {n : SimplexCategory} (α : (Δ[1] : SSet.{0}).obj (op n)) :
    M.obj (op (op n)) ⟶ M.obj (op (op n))
  /-- Evaluation at the constant zero simplex is the first endpoint. -/
  zero_endpoint (n : SimplexCategory) :
    hom (SSet.stdSimplex.const 1 0 (op n)) = a.app (op (op n))
  /-- Evaluation at the constant one simplex is the second endpoint. -/
  one_endpoint (n : SimplexCategory) :
    hom (SSet.stdSimplex.const 1 1 (op n)) = b.app (op (op n))
  /-- The indexed module maps are natural with scalar restriction. -/
  naturality {n₁ n₂ : SimplexCategory} (σ : n₁ ⟶ n₂)
      (α : (Δ[1] : SSet).obj (op n₂)) :
    M.map (op (op σ) : op (op n₁) ⟶ op (op n₂)) ≫
        (ModuleCat.restrictScalars _).map (hom α) =
      hom ((Δ[1] : SSet).map σ.op α) ≫
        M.map (op (op σ) : op (op n₁) ⟶ op (op n₂))

variable {R : (SimplexCategoryᵒᵖ)ᵒᵖ ⥤ RingCat.{u}}
variable {M : PresheafOfModules R} {a b : M ⟶ M}

/-- The constant homotopy has the prescribed zero endpoint. -/
theorem refl_zero_endpoint (a : M ⟶ M) (n : SimplexCategory) :
    a.app (op (op n)) = a.app (op (op n)) := sorry

/-- The constant homotopy has the prescribed one endpoint. -/
theorem refl_one_endpoint (a : M ⟶ M) (n : SimplexCategory) :
    a.app (op (op n)) = a.app (op (op n)) := sorry

/-- The constant homotopy satisfies scalar-compatible naturality. -/
theorem refl_naturality (a : M ⟶ M) {n₁ n₂ : SimplexCategory} (σ : n₁ ⟶ n₂)
    (α : (Δ[1] : SSet.{0}).obj (op n₂)) :
    M.map (op (op σ) : op (op n₁) ⟶ op (op n₂)) ≫
        (ModuleCat.restrictScalars _).map (a.app (op (op n₂))) =
      a.app (op (op n₁)) ≫
        M.map (op (op σ) : op (op n₁) ⟶ op (op n₂)) := sorry

/-- The endpoint and naturality laws of a module homotopy. -/
theorem spec (H : CosimplicialHomotopy M a b) :
    (∀ n : SimplexCategory,
      H.hom (SSet.stdSimplex.const 1 0 (op n)) = a.app (op (op n))) ∧
    (∀ n : SimplexCategory,
      H.hom (SSet.stdSimplex.const 1 1 (op n)) = b.app (op (op n))) ∧
    (∀ {n₁ n₂ : SimplexCategory} (σ : n₁ ⟶ n₂)
      (α : (Δ[1] : SSet).obj (op n₂)),
      M.map (op (op σ) : op (op n₁) ⟶ op (op n₂)) ≫
          (ModuleCat.restrictScalars _).map (H.hom α) =
        H.hom ((Δ[1] : SSet).map σ.op α) ≫
          M.map (op (op σ) : op (op n₁) ⟶ op (op n₂))) := sorry

/-- The constant simplex-indexed homotopy on an endomorphism. -/
def refl (a : M ⟶ M) : CosimplicialHomotopy M a a where
  hom {_} _ := a.app _
  zero_endpoint := refl_zero_endpoint a
  one_endpoint := refl_one_endpoint a
  naturality := refl_naturality a

end PresheafOfModules
