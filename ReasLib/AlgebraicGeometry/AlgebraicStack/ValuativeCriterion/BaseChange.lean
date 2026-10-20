/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Base change of the existence part of the valuative criterion

The existence part of the valuative criterion for morphisms of algebraic
stacks is stable under base change, both for arbitrary bilimit cones and
for the canonical projections of chosen 2-fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence

/-- The second projection of an algebraic bilimit 2-fibre product cone
satisfies the existence part of the valuative criterion whenever the
morphism being pulled back does. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Existence f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Existence c.snd := sorry

/-- The first projection of a chosen 2-fibre product of algebraic stacks
satisfies the existence part of the valuative criterion whenever the
second leg does. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Existence g] :
    Existence (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

/-- The second projection of a chosen 2-fibre product of algebraic stacks
satisfies the existence part of the valuative criterion whenever the
first leg does. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Existence f] :
    Existence (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence
