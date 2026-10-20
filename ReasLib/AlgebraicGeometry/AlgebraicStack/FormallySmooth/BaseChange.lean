/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormallySmooth
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Base change of formally smooth morphisms of algebraic stacks

Formally smooth morphisms of algebraic stacks are stable under arbitrary
bicategorical base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The second projection of the explicit two-fibre product of a formally smooth
morphism of algebraic stacks along any morphism of algebraic stacks is formally smooth. -/
instance FormallySmooth.twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [FormallySmooth f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    FormallySmooth (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Formally smooth morphisms of algebraic stacks remain formally smooth along
the second projection of any bilimit pseudopullback cone. -/
theorem FormallySmooth.of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [FormallySmooth f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    FormallySmooth c.snd :=
  sorry

end AlgebraicGeometry.AlgebraicStack
