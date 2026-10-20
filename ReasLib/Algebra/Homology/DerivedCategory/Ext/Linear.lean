/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear degree-zero Ext API

This file provides the inverse evaluation formula for the canonical degree-zero Ext
equivalence.  It is independent of projective resolutions and ideal-power quotients.
@stack 0EGY
@stack 0G3L
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u t

namespace CategoryTheory.Abelian.Ext

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]
variable {X Y : C}

/-- The canonical degree-zero Ext equivalence sends the class of a morphism back to that
morphism. -/
@[simp, stacks 0EGY "degree-zero Ext equivalence on morphism classes"]
theorem linearEquiv₀_mk₀ (f : X ⟶ Y) :
    (linearEquiv₀ (R := R) : Ext X Y 0 ≃ₗ[R] (X ⟶ Y)) (mk₀ f) = f := sorry

section CommRing

variable {S : Type t} [CommRing S] {D : Type u} [Category.{v} D] [Abelian D] [Linear S D]
  [HasExt.{w} D]

/-- Postcomposition by a degree-zero Ext class is ordinary composition of morphisms. -/
@[stacks 0G3L "degree-zero Ext postcomposition"]
theorem postcompOfLinear_mk₀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((mk₀ g).postcompOfLinear S X (add_zero 0)) (mk₀ f) = mk₀ (f ≫ g) := sorry

/-- Precomposition by a degree-zero Ext class is ordinary composition of morphisms. -/
@[stacks 0G3L "degree-zero Ext precomposition"]
theorem precompOfLinear_mk₀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((mk₀ f).precompOfLinear S Z (zero_add 0)) (mk₀ g) = mk₀ (f ≫ g) := sorry

end CommRing

end CategoryTheory.Abelian.Ext
