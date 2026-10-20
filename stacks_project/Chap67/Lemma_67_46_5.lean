/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.BaseChange
import StacksCheckRecall

/-!
# Base change of finite locally free morphisms of algebraic spaces

The base change of a finite locally free morphism of algebraic spaces by any
morphism of algebraic spaces is again a finite locally free morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.46.5: The base change of a finite locally free morphism is finite
locally free. -/
@[stacks 03ZY] #check
  (AlgebraicGeometry.AlgebraicSpace.finiteLocallyFree_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree S :
        MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
