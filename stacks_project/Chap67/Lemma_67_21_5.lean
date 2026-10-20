/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine.BaseChange
import StacksCheckRecall

/-!
# Base change of quasi-affine morphisms of algebraic spaces

The base change of a quasi-affine morphism of algebraic spaces by any morphism
of algebraic spaces is again a quasi-affine morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 67.21.5: The base change of a quasi-affine morphism is quasi-affine. -/
@[stacks 03WO] #check
  (AlgebraicGeometry.AlgebraicSpace.QuasiAffine.stableUnderBaseChange :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.QuasiAffine S :
          MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
