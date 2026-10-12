/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Lemma_101_39_12_Existence

/-!
# Base change of the existence part of the valuative criterion

The existence part of the valuative criterion for morphisms of algebraic
stacks is stable along the second projection of any bilimit 2-fibre product
cone, and along the first projection of a chosen 2-fibre product when that
leg satisfies existence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence

/-- Existence for morphisms of algebraic stacks remains along the second
projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Existence f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Existence c.snd := sorry

/-- The first projection of a chosen 2-fibre product satisfies the existence
part of the valuative criterion whenever the second leg does. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Existence g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Existence (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence
