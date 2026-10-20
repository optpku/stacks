/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness

/-!
# Base change of uniqueness for morphisms of algebraic stacks

Morphisms of algebraic stacks satisfying uniqueness remain unique along the
second projection of any bilimit 2-fibre product cone, and along the first
projection of a chosen 2-fibre product when that leg satisfies uniqueness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
namespace Uniqueness

/-- Morphisms of algebraic stacks satisfying uniqueness remain unique along
the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Uniqueness f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Uniqueness c.snd := sorry

/-- The first projection of a chosen 2-fibre product satisfies uniqueness
whenever the second leg is a morphism of algebraic stacks satisfying
uniqueness. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Uniqueness g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Uniqueness (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

/-- The second projection of a chosen 2-fibre product satisfies uniqueness
whenever the first leg is a morphism of algebraic stacks satisfying
uniqueness. -/
@[stacks 0CLH]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Uniqueness f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Uniqueness (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end Uniqueness
end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
