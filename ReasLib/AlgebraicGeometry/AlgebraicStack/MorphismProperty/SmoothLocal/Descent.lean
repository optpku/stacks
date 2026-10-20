module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.SmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Descent of smooth-local morphism properties of algebraic stacks

Properties of algebraic-space morphisms that are smooth local on source and
target and fppf local on the target descend for algebraic stacks along
surjective, flat, locally finitely presented base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAtSourceAndTarget

/-- The lift of a property of algebraic-space morphisms that is smooth local on
source and target and fppf local on the target descends along surjective, flat,
locally finitely presented base change of algebraic stacks. -/
@[stacks 0DN6]
theorem of_twoFibreProduct_snd {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g]
    [AlgebraicStack.Flat g] [AlgebraicStack.LocallyOfFinitePresentation g]
    (hP : hasSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :
    hasSmoothLocalAtSourceAndTarget P f :=
  sorry

/-- The lift of a property of algebraic-space morphisms that is smooth local on
source and target and fppf local on the target descends along the second
projection of any bilimit pseudopullback cone against a surjective, flat,
locally finitely presented morphism of algebraic stacks. -/
theorem of_isBilimit_snd {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] {f : X ⟶ Y} {g : Z ⟶ Y} [Surjective g]
    [AlgebraicStack.Flat g] [AlgebraicStack.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (hP : hasSmoothLocalAtSourceAndTarget P c.snd) :
    hasSmoothLocalAtSourceAndTarget P f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAtSourceAndTarget
