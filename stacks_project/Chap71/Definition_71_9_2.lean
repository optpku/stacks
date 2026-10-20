/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Relative
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.9.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. A relative effective Cartier divisor on `X/Y` is an
effective Cartier divisor `D ⊂ X` such that `D ⟶ Y` is a flat morphism of
algebraic spaces. -/
@[stacks 0EPP] #check
  (AlgebraicGeometry.AlgebraicSpace.IsRelativeEffectiveCartierDivisor :
    {S : Scheme.{u}} → {D X Y : AlgebraicSpace S} → (X ⟶ Y) → (D ⟶ X) → Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.isRelativeEffectiveCartierDivisor_iff :
    ∀ {S : Scheme.{u}} {D X Y : AlgebraicSpace S} (f : X ⟶ Y) (i : D ⟶ X),
      IsRelativeEffectiveCartierDivisor f i ↔
        IsEffectiveCartierDivisor i ∧ Flat (i ≫ f))
