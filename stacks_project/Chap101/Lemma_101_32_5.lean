/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleLocal.FiniteGroupoid
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids

universe u

/- Lemma 101.32.5: Let `X` be an algebraic stack. Assume `X` is quasi-DM with
separated diagonal (equivalently the inertia morphism `I_X ⟶ X` is locally
quasi-finite and separated, by Lemma 101.6.1). Let `x : Points X`. Assume `x`
can be represented by a quasi-compact morphism `Spec(k) ⟶ X`
(`existsQuasiCompactFieldValuedPoint`). Then there exists a morphism of
algebraic stacks `f : 𝒰 ⟶ X` such that there is a point `u : Points 𝒰`
mapping to `x` and `f` induces an isomorphism of residual gerbes at `u` and
`x`, `f` is `relativelyRepresentableByAlgebraicSpaces` and
`Groupoids.Hom.Etale`, and `𝒰 = (SmallQuotient.quotientStack (ofScheme G))` for a
groupoid scheme `(U, R, s, t, c)` with `IsAffine G.U.left`,
`IsAffine G.R.left`, and with `IsFinite`, `AlgebraicGeometry.Flat`, and
`AlgebraicGeometry.LocallyOfFinitePresentation` of both `G.s.left` and
`G.t.left`. -/
@[stacks 0DU5] #check
  (AlgebraicGeometry.AlgebraicStack.existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt_of_isQuasiDM :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiDM X],
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (diagonal.{u + 1, u, u + 1} X) →
      ∀ {x : Points X}, existsQuasiCompactFieldValuedPoint X x →
        existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt X x)
