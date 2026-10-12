/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

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

/-- Lemma 101.28.3: in a fibre product of algebraic stacks, if `X` is a gerbe
over `Y` then the base-changed stack is a gerbe over the changed base.

The source square is a bilimit `PseudoPullbackCone` for a gerbe morphism
`f : X ⟶ Y` and a morphism `g : Z ⟶ Y` of algebraic stacks; the gerbe-over
map is `c.snd`. -/
@[stacks 06QE]
theorem isGerbeMorphism_of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    (hf : IsGerbeMorphism (Scheme.fppfTopology.over S) f)
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] [c.IsBilimit] :
    IsGerbeMorphism (Scheme.fppfTopology.over S) c.snd :=
  sorry

/-- The second projection of a chosen 2-fibre product of algebraic stacks is a
gerbe morphism whenever the left cospan leg is a gerbe morphism. -/
theorem isGerbeMorphism_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsGerbeMorphism (Scheme.fppfTopology.over S) f)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsGerbeMorphism (Scheme.fppfTopology.over S)
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
