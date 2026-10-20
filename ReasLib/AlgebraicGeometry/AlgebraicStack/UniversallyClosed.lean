/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed

/-!
# Base change of universally closed morphisms of algebraic stacks

Universally closed morphisms of algebraic stacks remain universally closed
under arbitrary algebraic-stack base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyClosed

/-- Universally closed morphisms of algebraic stacks remain universally closed
along the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [UniversallyClosed f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    UniversallyClosed c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product is universally closed
whenever the second leg is a universally closed morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyClosed g] :
    UniversallyClosed (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversallyClosed

/-- The second projection of a chosen 2-fibre product is universally closed
whenever the first leg is a universally closed morphism of algebraic stacks. -/
instance universallyClosed_pullback_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyClosed f] :
    UniversallyClosed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
