module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

/-!
# Base change of gerbes of algebraic stacks

In a fibre product square of algebraic stacks, a relative gerbe remains a
relative gerbe after base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory FiberedCategoryOver.Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

section

variable {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] [c.IsBilimit]

/- Lemma 101.28.3: in a fibre product of algebraic stacks, if `X` is a gerbe
over `Y` then the base-changed stack is a gerbe over the changed base.

The source square is a bilimit `PseudoPullbackCone` for a gerbe morphism
`f : X ⟶ Y` and a morphism `g : Z ⟶ Y` of algebraic stacks; the gerbe-over
map is `c.snd`. -/
@[stacks 06QE]
#check (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism.baseChange
    (J := Scheme.fppfTopology.over S) c :
    IsGerbeMorphism (Scheme.fppfTopology.over S) f →
      IsGerbeMorphism (Scheme.fppfTopology.over S) c.snd)

end

section

variable {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]

/- The second projection of a chosen 2-fibre product of algebraic stacks is a
gerbe morphism whenever the left cospan leg is a gerbe morphism. -/
#check (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism.baseChange
    (J := Scheme.fppfTopology.over S)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f g) :
    IsGerbeMorphism (Scheme.fppfTopology.over S) f →
      IsGerbeMorphism (Scheme.fppfTopology.over S)
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

end

end AlgebraicGeometry.AlgebraicStack
