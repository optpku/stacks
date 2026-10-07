module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Lemma_101_44_4_LocalCompleteIntersection

/-!
# Flat base change of local complete intersection morphisms of algebraic stacks

Local complete intersection morphisms of algebraic stacks remain local complete
intersections along the second projection of any bilimit 2-fibre product cone
taken against a flat morphism, and along the first projection of a chosen
2-fibre product when that leg is a local complete intersection and the other
leg is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection

/-- Local complete intersection morphisms of algebraic stacks remain local
complete intersections along the second projection of any bilimit
`PseudoPullbackCone` taken against a flat morphism. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [IsLocalCompleteIntersection f] [Flat g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    IsLocalCompleteIntersection c.snd := sorry

/-- The second projection of a chosen 2-fibre product of a local complete
intersection morphism of algebraic stacks along a flat morphism is a local
complete intersection. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsLocalCompleteIntersection f] [Flat g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsLocalCompleteIntersection (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- The first projection of a chosen 2-fibre product is a local complete
intersection whenever the second leg is a local complete intersection morphism
of algebraic stacks and the first leg is flat. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat f] [IsLocalCompleteIntersection g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsLocalCompleteIntersection (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection
