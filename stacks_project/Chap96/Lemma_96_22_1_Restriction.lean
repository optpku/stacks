/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.AbelianRestriction

/-!
# Restriction of abelian étale sheaves along a representing algebraic space

The restriction functor is continuous sheaf pushforward along the small étale comparison.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

universe u

/-- Restriction of abelian étale sheaves to a representing algebraic space is additive. -/
instance AlgebraicGeometry.GroupoidsOver.restrictAbelian.instAdditive
    {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : F.toGroupoids ≌ X) :
    (AlgebraicGeometry.GroupoidsOver.restrictAbelian e).Additive :=
  CategoryTheory.Functor.sheafPushforwardContinuous_additive
    (AlgebraicGeometry.GroupoidsOver.smallEtaleFunctor F X e)
    (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology

#check (AlgebraicGeometry.GroupoidsOver.restrictAbelian :
    ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S},
      (F.toGroupoids ≌ X) →
        Sheaf X.etaleTopology AddCommGrpCat.{u} ⥤
          Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u})
