module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Lemma_101_25_5_Flat

/-!
# Base change of flat morphisms of algebraic stacks

Flat morphisms of algebraic stacks remain flat along the second projection of
any bilimit 2-fibre product cone, and along the first projection of a chosen
2-fibre product when that leg is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Flat

/-- Flat morphisms of algebraic stacks remain flat along the second projection
of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Flat f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Flat c.snd := sorry

/-- The first projection of a chosen 2-fibre product is flat whenever the
second leg is a flat morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Flat (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack.Flat
