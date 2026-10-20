/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.EllipticCurve.AlgebraicStack

/-! The algebraic-stack condition and scheme-level surjectivity for elliptic curves. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.EllipticCurve
open scoped Bicategory

universe u

#check (AlgebraicGeometry.EllipticCurve.Moduli.IsAlgebraicStack.{u} : Prop)

#check (AlgebraicGeometry.EllipticCurve.Moduli.surjectiveOnSchemes_iff :
  ∀ {U : Over Moduli.specInt.{u}} (p : GroupoidsOver.slice U ⟶ moduli.{u}),
    Moduli.surjectiveOnSchemes p ↔
      ∀ ⦃S' : Over Moduli.specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
        (W : Over Moduli.specInt.{u}) (π : W ⟶ S'),
        Groupoids.Hom.RepresentsSchemeBaseChange p g W π →
          AlgebraicGeometry.Surjective π.left)
