/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleLocal.FiniteGroupoid
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 101.32.3: Let `X` be an algebraic stack. Assume `X` is quasi-DM with
separated diagonal (equivalently the inertia morphism `I_X ⟶ X` is locally
quasi-finite and separated). Let `x : AlgebraicStack.Points X`. Then there
exists a morphism of algebraic stacks `𝒰 ⟶ X` hitting `x`, representable by
algebraic spaces and étale, where `𝒰 = [U/R]` for a groupoid scheme
`(U, R, s, t, c)` with `U`, `R` affine and `s`, `t` finite, flat, and locally
of finite presentation. -/
@[stacks 0DU3] #check
  (AlgebraicGeometry.AlgebraicStack.existsEtaleLocalAffineFiniteGroupoidAt_of_isQuasiDM :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [AlgebraicStack.IsQuasiDM X],
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (diagonal.{u + 1, u, u + 1} X) →
      ∀ (x : AlgebraicStack.Points X),
        AlgebraicStack.existsEtaleLocalAffineFiniteGroupoidAt X x)
