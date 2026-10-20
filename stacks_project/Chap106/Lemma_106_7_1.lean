/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.InfinitesimalAutomorphisms
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

/- Lemma 106.7.1. Infinitesimal automorphism modules of an algebraic stack with
locally finitely presented inertia commute with flat extension of scalars. -/
@[stacks 0DNR] #check (AlgebraicGeometry.GroupoidsOver.infExtendScalars_isIso :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Groupoids.Hom.LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X)]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB) (hflat : v.hom.Flat)
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A),
    IsIso (infExtendScalars v hv x M))
