module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Lemma_101_36_4_Unramified

/-!
# Base change of unramified morphisms of algebraic stacks

Unramified morphisms of algebraic stacks remain unramified along the second
projection of any bilimit 2-fibre product cone, and along the first projection
of a chosen 2-fibre product when that leg is unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

/-- Unramified morphisms of algebraic stacks remain unramified along the second
projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Unramified f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Unramified c.snd := sorry

/-- The first projection of a chosen 2-fibre product is unramified whenever the
second leg is an unramified morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Unramified g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Unramified (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack.Unramified
