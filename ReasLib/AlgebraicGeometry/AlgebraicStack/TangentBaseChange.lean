/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.StrongRimSchlessinger

/-!
# Flat base change of infinitesimal deformation modules

For an algebraic stack locally of finite presentation over a scheme,
the canonical comparison on tangent modules is an isomorphism along flat
extensions of scalars.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- For an algebraic stack locally of finite presentation over `S`, the
canonical comparison `T_x(M) ⊗[A] B ⟶ T_y(M ⊗[A] B)` is an isomorphism
along every flat `S`-algebra map `A ⟶ B`, where `y` is the restriction of `x`. -/
theorem tangentExtendScalars_isIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation
      (baseProjection.{u + 1, u, u + 1} X)]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB) (hflat : v.hom.Flat)
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    IsIso (tangentExtendScalars v hv x M) :=
  sorry

/-- The tangent scalar-extension comparison for an algebraic stack locally of
finite presentation is invertible when the target ring is flat as a module
over the source ring through the given ring map. -/
instance instIsIso_tangentExtendScalars {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation
      (baseProjection.{u + 1, u, u + 1} X)]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    [Module.Flat A ((ModuleCat.restrictScalars v.hom).obj (ModuleCat.of B B))]
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    IsIso (tangentExtendScalars v hv x M) := by
  apply tangentExtendScalars_isIso v hv
  exact ‹Module.Flat A ((ModuleCat.restrictScalars v.hom).obj (ModuleCat.of B B))›

end AlgebraicGeometry.GroupoidsOver
