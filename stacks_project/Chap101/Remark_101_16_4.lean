module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Definition_101_16_2_SmoothLocal

/-!
# Base change of smooth-local-on-source-and-target morphisms of algebraic stacks

If a morphism property of algebraic spaces is smooth local on the
source-and-target and stable under base change, then so is its lift to
morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace hasSmoothLocalAtSourceAndTarget

/-- Remark 101.16.4: if a morphism property `P` of algebraic spaces is smooth
local on the source-and-target and stable under base change, then the lift of
`P` to morphisms of algebraic stacks from Definition 101.16.2 is also stable
under base change. In particular, if `f : X ⟶ Y` has
`hasSmoothLocalAtSourceAndTarget P`, then so does the projection
`TwoFibreProduct.snd f g` (Stacks writes `Y' ×_Y X ⟶ Y'`). -/
@[stacks 06FQ]
theorem twoFibreProduct_snd {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : hasSmoothLocalAtSourceAndTarget P f)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    hasSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Morphisms of algebraic stacks satisfying
`hasSmoothLocalAtSourceAndTarget P` remain so along the second projection of
any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} (hf : hasSmoothLocalAtSourceAndTarget P f)
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    hasSmoothLocalAtSourceAndTarget P c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product satisfies
`hasSmoothLocalAtSourceAndTarget P` whenever the second leg does. -/
theorem twoFibreProduct_fst {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hg : hasSmoothLocalAtSourceAndTarget P g)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    hasSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end hasSmoothLocalAtSourceAndTarget

end AlgebraicGeometry.AlgebraicStack
