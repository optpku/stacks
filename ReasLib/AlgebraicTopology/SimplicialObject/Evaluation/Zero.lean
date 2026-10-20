/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Functor.Const.Adjunction

/-!
# Evaluation of simplicial objects in degree zero

The zero simplex is terminal in `SimplexCategory`, hence initial in the indexing category of
simplicial objects.  This file owns degree-zero evaluation and the resulting specialization of
the constant-diagram adjunction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- Evaluation of a simplicial object in degree zero. -/
@[stacks 0182 "simplicial degree-zero evaluation"]
abbrev evalZero : SimplicialObject C ⥤ C :=
  (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋0⦌)

/-- Degree-zero evaluation sends a simplicial object to its object of zero-simplices. -/
@[simp, stacks 0182 "simplicial degree-zero evaluation on objects"]
theorem evalZero.obj (X : SimplicialObject C) :
    (evalZero (C := C)).obj X = X _⦋0⦌ := sorry

/-- Degree-zero evaluation sends a simplicial morphism to its degree-zero component. -/
@[simp, stacks 0182 "simplicial degree-zero evaluation on morphisms"]
theorem evalZero.map {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (evalZero (C := C)).map f = f.app (op ⦋0⦌) := sorry

/-- Maps from a constant simplicial object are classified by their degree-zero component. -/
@[stacks 0G5Q "constant simplicial object degree-zero Hom equivalence"]
def evalZero.constHomEquiv (Z : C) (X : SimplicialObject C) :
    ((const C).obj Z ⟶ X) ≃ (Z ⟶ X _⦋0⦌) :=
  SimplexCategory.isTerminalZero.op.constHomEquiv Z X

/-- The constant simplicial object functor is left adjoint to degree-zero evaluation. -/
@[stacks 0G5Q "constant simplicial object degree-zero adjunction"]
def evalZero.constAdj : const C ⊣ evalZero :=
  SimplexCategory.isTerminalZero.op.constAdj

end CategoryTheory.SimplicialObject
