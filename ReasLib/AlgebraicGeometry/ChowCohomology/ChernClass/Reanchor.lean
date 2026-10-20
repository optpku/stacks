/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass

/-- Regard a base-wide Chern-class theory as anchored at another `S`-scheme. -/
def Theory.reanchor {S X : Scheme.{u}} {δ : S → ℤ} {π : X ⟶ S}
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (Y : Over S) [LocallyOfFiniteType Y.hom] :
    Theory δ Y.hom where
  baseComponent := classes.baseComponent
  component_pullback := classes.component_pullback
  component_one_cap := classes.component_one_cap
  component_zero := classes.component_zero
  component_iso := classes.component_iso
  component_eq_zero_of_rank_lt := classes.component_eq_zero_of_rank_lt
  component_mem_center := classes.component_mem_center
  component_biprod := classes.component_biprod
  component_one_tensor := classes.component_one_tensor
  splitting_principle := classes.splitting_principle

/-- Reanchoring does not change the base-wide Chern components. -/
theorem Theory.reanchor_baseComponent {S X : Scheme.{u}} {δ : S → ℤ} {π : X ⟶ S}
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (Y Z : Over S) [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (E : Z.left.Modules) (i : ℕ) :
    (classes.reanchor Y).baseComponent Z E i = classes.baseComponent Z E i := sorry

end AlgebraicGeometry.ChernClass
