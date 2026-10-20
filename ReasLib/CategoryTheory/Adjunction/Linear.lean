/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear Adjunctions

This leaf supplies the linear Hom equivalence of a linear adjunction and propagates linearity
between its two adjoints.  It is the linear counterpart of Mathlib's additive adjunction API.
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {k : Type w} [Semiring k]
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Preadditive C] [Preadditive D]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

/-- A right adjoint of a linear functor between linear categories is linear. -/
@[stacks 09LN "linearity of a right adjoint"]
lemma right_adjoint_linear [F.Linear k] : G.Linear k := sorry

/-- A left adjoint of a linear functor between linear categories is linear. -/
@[stacks 09LN "linearity of a left adjoint"]
lemma left_adjoint_linear [G.Linear k] : F.Linear k := sorry

/-- The Hom equivalence of an adjunction whose left adjoint is linear, promoted to a linear
equivalence.  Linearity of the right adjoint is a consequence, not an input. -/
@[stacks 09LN "linear Hom equivalence of a linear adjunction"]
def homLinearEquiv [F.Additive] [F.Linear k] (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ₗ[k] (X ⟶ G.obj Y) where
  toAddEquiv := adj.homAddEquiv X Y
  map_smul' := sorry

/-- The forward map of `homLinearEquiv` is adjunction currying. -/
@[simp]
lemma homLinearEquiv_apply [F.Additive] [F.Linear k]
    (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homLinearEquiv (k := k) X Y f = adj.homEquiv X Y f := sorry

/-- The inverse map of `homLinearEquiv` is adjunction uncurrying. -/
@[simp]
lemma homLinearEquiv_symm_apply [F.Additive] [F.Linear k]
    (X : C) (Y : D) (g : X ⟶ G.obj Y) :
    (adj.homLinearEquiv (k := k) X Y).symm g =
      (adj.homEquiv X Y).symm g := sorry

end CategoryTheory.Adjunction
