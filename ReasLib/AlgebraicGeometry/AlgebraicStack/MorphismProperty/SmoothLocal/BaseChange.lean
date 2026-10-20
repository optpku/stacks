module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.SmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Base change of smooth-local morphism properties of algebraic stacks

A property of algebraic-space morphisms that is smooth local on source and
target and stable under base change lifts to a base-change-stable property of
algebraic-stack morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace hasSmoothLocalAtSourceAndTarget

/-- If a property of algebraic-space morphisms is smooth local on source and
target and stable under base change, its lift to algebraic-stack morphisms is
preserved by the second projection of a chosen 2-fibre product. -/
@[stacks 06FQ]
theorem twoFibreProduct_snd {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : hasSmoothLocalAtSourceAndTarget P f) :
    hasSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- If a property of algebraic-space morphisms is smooth local on source and
target and stable under base change, its lift to algebraic-stack morphisms is
preserved by the second projection of any bilimit pseudopullback cone. -/
theorem of_isBilimit {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} (hf : hasSmoothLocalAtSourceAndTarget P f)
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    hasSmoothLocalAtSourceAndTarget P c.snd :=
  sorry

/-- If a property of algebraic-space morphisms is smooth local on source and
target and stable under base change, the first projection of a chosen 2-fibre
product has its lift whenever the second leg does. -/
theorem twoFibreProduct_fst {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hg : hasSmoothLocalAtSourceAndTarget P g) :
    hasSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end hasSmoothLocalAtSourceAndTarget

end AlgebraicGeometry.AlgebraicStack
