/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Reduction

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Joint reflection of the reduction relation and its existential projection,
with their bounded interpretations, makes an object property closed under reductions. -/
theorem reduction_mem_of_joint_reflection
    {P : ObjectProperty Scheme.{u}}
    (red red_bounded : Scheme.{u} → Scheme.{u} → Prop)
    (hasRed hasRed_bounded : Scheme.{u} → Prop)
    (red_spec : ∀ X Y, red X Y ↔ Y = reduction X)
    (hasRed_spec : ∀ X, hasRed X ↔ ∃ Y, red X Y)
    (red_reflection : ∀ {X Y}, P X →
      (red_bounded X Y ↔ red X Y ∧ P Y))
    (hasRed_reflection : ∀ {X}, P X →
      (hasRed_bounded X ↔ hasRed X))
    (hasRed_bounded_spec : ∀ X, hasRed_bounded X ↔ ∃ Y, red_bounded X Y)
    {X : Scheme.{u}} (hX : P X) :
    P (reduction X) := sorry

end AlgebraicGeometry.Scheme
