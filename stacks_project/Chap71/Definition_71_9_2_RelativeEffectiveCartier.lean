/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Relative

/-!
# Relative effective Cartier divisors on algebraic spaces

A morphism of algebraic spaces `i : D ⟶ X` is a relative effective Cartier
divisor over `f : X ⟶ Y` when it is an effective Cartier divisor and the
composite `i ≫ f : D ⟶ Y` is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.IsRelativeEffectiveCartierDivisor :
    {S : Scheme.{u}} → {D X Y : AlgebraicSpace S} → (X ⟶ Y) → (D ⟶ X) → Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.isRelativeEffectiveCartierDivisor_iff :
    ∀ {S : Scheme.{u}} {D X Y : AlgebraicSpace S} (f : X ⟶ Y) (i : D ⟶ X),
      IsRelativeEffectiveCartierDivisor f i ↔
        IsEffectiveCartierDivisor i ∧ Flat (i ≫ f))
