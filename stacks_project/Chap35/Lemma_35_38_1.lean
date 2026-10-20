/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty.QuasiAffine
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.38.1: Every scheme descent datum over an fpqc covering whose component
structure morphisms are quasi-affine is effective. -/
@[stacks 0247] #check (AlgebraicGeometry.QuasiAffineHom.satisfiesDescentFpqc :
    CategoryTheory.MorphismProperty.SatisfiesDescent
      (@AlgebraicGeometry.QuasiAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) .fpqc)
