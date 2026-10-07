module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap101.Definition_101_9_1_Affine

/-!
# Base change of affine morphisms of algebraic stacks

Affine morphisms of algebraic stacks remain affine along the second projection
of any bilimit 2-fibre product cone, and along the first projection of a chosen
2-fibre product when that leg is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom
namespace Affine

/-- Affine morphisms of algebraic stacks remain affine along the second
projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Affine f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Affine c.snd := sorry

/-- The first projection of a chosen 2-fibre product is affine whenever the
second leg is an affine morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Affine g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Affine (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

end Affine
end AlgebraicGeometry.Groupoids.Hom
