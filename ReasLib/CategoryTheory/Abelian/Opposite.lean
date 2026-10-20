/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Preadditive.Opposite

/-!
# Recovering an abelian category from its opposite

Mathlib supplies the canonical instance `Abelian C → Abelian Cᵒᵖ`.  The reverse construction is
provided explicitly so that the two directions do not form a typeclass-search cycle.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Abelian

variable (C : Type u) [Category.{v} C]

/-- Recover an abelian structure on `C` from an abelian structure on `Cᵒᵖ`.  This definition is
deliberately not an instance. -/
@[stacks 010A, implicit_reducible]
noncomputable def ofOpposite [Abelian Cᵒᵖ] : Abelian C :=
  @abelianOfEquivalence C _ (Preadditive.ofOpposite C)
    (Preadditive.hasFiniteProductsOfOpposite C) Cᵒᵖᵒᵖ _
    (instAbelianOpposite Cᵒᵖ) (opOpEquivalence C).symm.functor inferInstance

end CategoryTheory.Abelian
