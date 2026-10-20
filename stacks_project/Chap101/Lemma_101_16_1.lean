/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.SmoothLocal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.16.1. Smooth-local criteria for properties of morphisms of algebraic stacks. -/
@[stacks 06FM] #check (AlgebraicGeometry.AlgebraicStack.forallSmoothComparison_iff_existsSurjectiveSmoothSquare :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] (f : X ⟶ Y),
    forallSmoothComparison P f ↔ existsSurjectiveSmoothSquare P f)

#check (AlgebraicGeometry.AlgebraicStack.forallSmoothComparison_iff_eval :
    ∀ {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    {U V : AlgebraicSpace S} (f : U.toGroupoids ⟶ V.toGroupoids),
    forallSmoothComparison P f ↔ P (AlgebraicSpace.toGroupoids.eval f))

#check (AlgebraicGeometry.AlgebraicStack.forallSmoothComparison_iff_has :
    ∀ {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f),
    forallSmoothComparison P f ↔ Groupoids.Hom.has P f)

#check (AlgebraicGeometry.AlgebraicStack.forallSmoothComparison_iff_recover :
    ∀ {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    {U V : AlgebraicSpace S} (eX : X ≌ U.toGroupoids)
    (eY : Y ≌ V.toGroupoids) (f : X ⟶ Y),
    forallSmoothComparison P f ↔
      P (AlgebraicSpace.toGroupoids.recover eX eY f))

end AlgebraicGeometry.AlgebraicStack
