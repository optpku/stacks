/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- 36.3.5.1: For `X = Spec A`, the derived global-sections functor
`RΓ(X, -) : D_QCoh(𝒪_X) ⥤ D(A)`. -/
@[stacks 06VU] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSections :
    (A : CommRingCat.{u}) → AlgebraicGeometry.Scheme.DerivedQCoh (Spec A) ⥤
      DerivedCategory (ModuleCat A))
