module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine.BaseChange
import StacksCheckRecall

/-!
# Base change of affine morphisms of algebraic stacks

The base change of an affine morphism of algebraic stacks by any morphism of
algebraic stacks is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom
namespace Affine

/- Lemma 101.9.2: Let `X ⟶ Y` be a morphism of algebraic stacks. Let
`Z ⟶ Y` be an affine morphism of algebraic stacks. Then
`Z ×_Y X ⟶ X` is an affine morphism of algebraic stacks.

Stacks writes the base change as `Z ×_Y X ⟶ X`. In the Lean type below,
`X` names the source's `Z` and `Z` names the source's `X`, so the projection is
`TwoFibreProduct.snd f g` of an affine `f` along an arbitrary morphism `g`. -/
@[stacks 0CHR] #check
  (AlgebraicGeometry.Groupoids.Hom.Affine.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Affine f],
    Affine (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

end Affine
end AlgebraicGeometry.Groupoids.Hom
