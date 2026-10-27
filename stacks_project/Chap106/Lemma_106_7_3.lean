/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TangentBaseChange

/-!
# Base change of infinitesimal deformation modules

For an algebraic stack whose structure morphism is locally of finite
presentation, infinitesimal lifts commute with flat extension of scalars of
the structure ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

/- Lemma 106.7.3. Let `X` be an algebraic stack over a scheme `S` whose
structure morphism `X ⟶ S` is locally of finite presentation. Let `A ⟶ B`
be a flat `S`-algebra homomorphism. Let `x` be an object of `X` over `A`
and set `y = x|_B`. Then the canonical comparison
`T_x(M) ⊗[A] B ⟶ T_y(M ⊗[A] B)` is an isomorphism. -/
@[stacks 0DNT] #check
  (AlgebraicGeometry.GroupoidsOver.tangentExtendScalars_isIso :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation
      (baseProjection.{u + 1, u, u + 1} X)]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB) (hflat : v.hom.Flat)
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A),
      IsIso (tangentExtendScalars v hv x M))
