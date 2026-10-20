/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact.BaseChange

/-!
# Base change of quasi-finite morphisms of algebraic stacks

Quasi-finite morphisms of algebraic stacks remain quasi-finite under base
change, both for arbitrary bilimit cones and for the canonical projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiFinite

/-- Quasi-finite morphisms of algebraic stacks remain quasi-finite along the
second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [QuasiFinite f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    QuasiFinite c.snd := sorry

/-- The first projection of a chosen 2-fibre product is quasi-finite whenever
the second leg is a quasi-finite morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiFinite g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    QuasiFinite (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

/-- The second projection of a chosen 2-fibre product is quasi-finite whenever
the first leg is a quasi-finite morphism of algebraic stacks. -/
@[stacks 0G2P]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiFinite f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    QuasiFinite (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiFinite
