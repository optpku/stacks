/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.BaseChange
public import stacks_project.Chap67.Lemma_67_20_5_Pullback

/-!
# Base change of affine morphisms of algebraic spaces

The base change of an affine morphism of algebraic spaces by any morphism of
algebraic spaces is again an affine morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.20.5: The base change of an affine morphism of algebraic spaces is
affine. -/
@[stacks 03WI] #check (AlgebraicGeometry.AlgebraicSpace.affine_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
    (@AlgebraicGeometry.AlgebraicSpace.Affine S : MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
