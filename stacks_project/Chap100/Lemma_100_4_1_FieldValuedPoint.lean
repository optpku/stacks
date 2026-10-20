/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

/-!
# Field-valued points of an algebraic stack

The field-valued-point constructor is provided by the shared mathematical owner.
-/

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.of :
  {S : Scheme.{u}} → {X : GroupoidsOver S} →
    (K : Type u) → [Field K] → (structureHom : Spec (.of K) ⟶ S) →
      (GroupoidsOver.slice (Over.mk structureHom) ⟶ X) →
        AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
