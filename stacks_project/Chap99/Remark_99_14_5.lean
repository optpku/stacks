/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BaseChange
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_33_1_Affine
public import stacks_project.Chap99.Situation_99_14_1
import StacksCheckRecall

/-!
# Polarized objects over an algebraic space

For an algebraic space `B` over `Spec ℤ`, the category `B-Polarized` consists of
polarized objects together with a morphism from the base scheme into `B`. It sits in a 2-fibre
product square over Polarized along schemes over `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The functor sending a scheme to itself as an object of `Sch / Spec ℤ`. -/
abbrev toOverSpecZ : Scheme.{u} ⥤ Over specZ :=
  AlgebraicGeometry.AlgebraicSpace.baseChangeToOverSpecZ

/-- The category of polarized objects whose base scheme maps to `B`. -/
abbrev polarizedOver (B : AlgebraicSpace specZ) :=
  AlgebraicGeometry.AlgebraicSpace.categoryBaseChange p B

namespace polarizedOver

/-- Package a polarized object with a morphism from its base scheme into `B`. -/
def mk {B : AlgebraicSpace specZ} (ξ : Obj)
    (h : ofOver (toOverSpecZ.obj ξ.S) ⟶ B) : polarizedOver B :=
  AlgebraicGeometry.AlgebraicSpace.categoryBaseChange.mk ξ h

/-- A morphism in `polarizedOver B` commutes with the structural maps to `B`. -/
theorem hom_spec {B : AlgebraicSpace specZ} {x y : polarizedOver B} (α : x ⟶ y) :
    (ofOverFunctor specZ).map (toOverSpecZ.map α.left.base) ≫ y.hom = x.hom := by
  exact AlgebraicGeometry.AlgebraicSpace.categoryBaseChange.hom_spec α

/-- The commutative projection square for `polarizedOver B`. -/
def square (B : AlgebraicSpace specZ) :
    CatCommSqOver (p ⋙ toOverSpecZ) (CostructuredArrow.proj (ofOverFunctor specZ) B)
      (polarizedOver B) :=
  AlgebraicGeometry.AlgebraicSpace.categoryBaseChange.square p B

end polarizedOver

#check (toOverSpecZ : Scheme.{u} ⥤ Over specZ)
#check (polarizedOver : AlgebraicSpace specZ → Type (u + 1))
#check (polarizedOver.mk : ∀ {B : AlgebraicSpace specZ} (ξ : Obj),
  (ofOver (toOverSpecZ.obj ξ.S) ⟶ B) → (polarizedOver B))
#check (polarizedOver.hom_spec : ∀ {B : AlgebraicSpace specZ} {x y : polarizedOver B}
  (α : x ⟶ y), (ofOverFunctor specZ).map (toOverSpecZ.map α.left.base) ≫ y.hom = x.hom)

/- Remark 99.14.5: for an algebraic space `B` over `Spec ℤ`, the category `B-Polarized` of
polarized families equipped with a map from their base to `B` sits in a 2-fibre product square
over `Polarized` and schemes over `B`. -/
@[stacks 0D1N]
#check (AlgebraicGeometry.AlgebraicSpace.categoryBaseChange.comparisonEquivalence (p := p) :
  ∀ (B : AlgebraicSpace specZ), polarizedOver B ≌
    CategoryTheory.Limits.CategoricalPullback (p ⋙ toOverSpecZ)
      (CategoryTheory.CostructuredArrow.proj
        AlgebraicGeometry.AlgebraicSpace.categoryBaseChange.ofOverFunctor B))

@[stacks 0D1N]
#check (AlgebraicGeometry.AlgebraicSpace.categoryBaseChange.instSquareIsBilimit (p := p) : ∀ (B : AlgebraicSpace specZ),
  CatCommSqOver.Resized.IsBilimit (polarizedOver.square B))

end AlgebraicGeometry.Polarized
