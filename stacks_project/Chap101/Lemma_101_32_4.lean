/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleLocal.FiniteGroupoid
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 101.32.4: A quasi-DM algebraic stack with separated diagonal admits,
at a point with finite automorphism group, a representable étale chart
inducing an isomorphism on automorphism groups and presented by an affine
groupoid scheme with finite, flat, locally finitely presented source and target. -/
@[stacks 0DU4] #check
  (AlgebraicGeometry.AlgebraicStack.existsEtaleLocalAffineFiniteGroupoidIsoAutAt_of_isQuasiDM :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiDM X],
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (diagonal.{u + 1, u, u + 1} X) →
      ∀ {x : Points X}, automorphismGroup.IsFinite x →
        existsEtaleLocalAffineFiniteGroupoidIsoAutAt X x)
