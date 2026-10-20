/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
import StacksCheckRecall

/-!
# Composition of quasi-affine morphisms of algebraic spaces

The composition of quasi-affine morphisms of algebraic spaces is quasi-affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

/- Lemma 67.21.4: The composition of quasi-affine morphisms is quasi-affine. -/
@[stacks 03WN] #check
  (AlgebraicGeometry.AlgebraicSpace.QuasiAffine.stableUnderComposition :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.AlgebraicSpace.QuasiAffine S :
          MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

#check
  (AlgebraicGeometry.AlgebraicSpace.QuasiAffine.comp :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.AlgebraicSpace.QuasiAffine f]
      [AlgebraicGeometry.AlgebraicSpace.QuasiAffine g],
      AlgebraicGeometry.AlgebraicSpace.QuasiAffine (f ≫ g))
