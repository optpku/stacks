/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.EllipticCurve.AlgebraicStack
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.EllipticCurve AlgebraicGeometry.EllipticCurve.Moduli
open scoped Bicategory

universe u

/- Definition 105.5.1: we say M_{1,1} is an algebraic stack if and only if we
have descent for objects for the étale topology on Sch, the key fact holds, and
there exists a surjective smooth morphism S ⟶ M_{1,1}. -/
@[stacks 072R] #check
  (AlgebraicGeometry.EllipticCurve.Moduli.IsAlgebraicStack.iff :
    IsAlgebraicStack.{u} ↔
      IsStack.InGroupoids (Scheme.etaleTopology.over specInt.{u}) moduli.{u}.p ∧
        FiberedCategoryOver.Groupoids.relativelyRepresentable
            (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} moduli.{u}) ∧
          ∃ (U : Over specInt.{u}) (p : GroupoidsOver.slice U ⟶ moduli.{u}),
            Groupoids.Hom.SmoothOnSchemes p ∧
              ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
                (W : Over specInt.{u}) (π : W ⟶ S'),
                Groupoids.Hom.RepresentsSchemeBaseChange p g W π →
                  AlgebraicGeometry.Surjective π.left)
