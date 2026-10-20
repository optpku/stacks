/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Relative effective Cartier divisors on algebraic spaces

A morphism of algebraic spaces `i : D ⟶ X` is a relative effective Cartier
divisor over `f : X ⟶ Y` when it is an effective Cartier divisor and the
composite `i ≫ f : D ⟶ Y` is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `i : D ⟶ X` of algebraic spaces over `S` is a relative effective
Cartier divisor with respect to `f : X ⟶ Y` when it is an effective Cartier
divisor and the composite `i ≫ f : D ⟶ Y` is flat. -/
class IsRelativeEffectiveCartierDivisor {S : Scheme.{u}} {D X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (i : D ⟶ X) : Prop
    extends IsEffectiveCartierDivisor i, Flat (i ≫ f)

/-- An effective Cartier divisor whose composite with the structure morphism is
flat is a relative effective Cartier divisor. -/
instance instOf_isEffectiveCartierDivisor_flat {S : Scheme.{u}}
    {D X Y : AlgebraicSpace S} (f : X ⟶ Y) (i : D ⟶ X)
    [IsEffectiveCartierDivisor i] [Flat (i ≫ f)] :
    IsRelativeEffectiveCartierDivisor f i where

/-- Relative effective Cartier divisors are exactly effective Cartier divisors
whose composite with the structure morphism is flat. -/
theorem isRelativeEffectiveCartierDivisor_iff {S : Scheme.{u}}
    {D X Y : AlgebraicSpace S} (f : X ⟶ Y) (i : D ⟶ X) :
    IsRelativeEffectiveCartierDivisor f i ↔
      IsEffectiveCartierDivisor i ∧ Flat (i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
