/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.AlgebraExtension
public import stacks_project.Chap91.Lemma_91_7_3
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

universe u

/- Lemma 91.7.4 For every morphism of ringed spaces and every module sheaf on its source,
square-zero relative algebra extensions with that identified kernel are canonically
classified by Ext¹ of the naive cotangent complex. -/
@[stacks 0GPZ] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Solution.extensionEquiv :
    {S X : RingedSpace.{u}} → (f : X ⟶ S) → (G : X.Modules) →
      Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
        (DerivedCategory.Q (C := X.Modules)).obj
          ((CochainComplex.singleFunctor X.Modules 0).obj G)) ≃
        IsoClass (𝟙 S) f G (zeroKernelMap f G))
