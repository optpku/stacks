/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Constant morphisms of algebraic spaces

A morphism of algebraic spaces over a base is constant when it factors through
the structural morphism from its source to that base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over `S` factors through the base algebraic space. -/
def IsConstant {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∃ g : ofOver (Over.mk (𝟙 S)) ⟶ Y, SchemeRealization.toBase X ≫ g = f

/-- A morphism is constant exactly when it factors through the structural morphism of its source. -/
theorem isConstant_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsConstant f ↔ ∃ g : ofOver (Over.mk (𝟙 S)) ⟶ Y,
      SchemeRealization.toBase X ≫ g = f :=
  sorry

/-- Composing the structural morphism with a morphism from the base gives a constant morphism. -/
theorem isConstant_comp_toBase {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (X : AlgebraicSpace S) (g : ofOver (Over.mk (𝟙 S)) ⟶ Y) :
    IsConstant (SchemeRealization.toBase X ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
