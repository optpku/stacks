/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
import StacksCheckRecall

/-!
# Base change of relative property (β), decent, and reasonable morphisms

Having property (β), being decent, or being reasonable is preserved under arbitrary
base change of morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 68.17.4 (1): Having property (β) is preserved under arbitrary base change. -/
@[stacks 03L0] #check (AlgebraicGeometry.AlgebraicSpace.propertyBeta_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
    (@AlgebraicGeometry.AlgebraicSpace.PropertyBeta _ : MorphismProperty (AlgebraicSpace S)))

/- Lemma 68.17.4 (2): Being decent is preserved under arbitrary base change. -/
@[stacks 03L0] #check (AlgebraicGeometry.AlgebraicSpace.decent_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
    (@AlgebraicGeometry.AlgebraicSpace.Decent _ : MorphismProperty (AlgebraicSpace S)))

/- Lemma 68.17.4 (3): Being reasonable is preserved under arbitrary base change. -/
@[stacks 03L0] #check (AlgebraicGeometry.AlgebraicSpace.reasonable_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
    (@AlgebraicGeometry.AlgebraicSpace.Reasonable _ : MorphismProperty (AlgebraicSpace S)))
