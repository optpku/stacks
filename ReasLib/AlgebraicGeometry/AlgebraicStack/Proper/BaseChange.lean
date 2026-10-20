/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyClosed

/-!
# Base change of proper morphisms of algebraic stacks

Proper morphisms of algebraic stacks remain proper along bilimit
pseudopullback cones and the canonical 2-fibre product projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Proper

/-- Proper morphisms of algebraic stacks remain proper along the second
projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Proper f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Proper c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product is proper whenever the
second leg is a proper morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Proper g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Proper (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- The second projection of a chosen 2-fibre product is proper whenever the
first leg is a proper morphism of algebraic stacks. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Proper f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Proper (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Proper
