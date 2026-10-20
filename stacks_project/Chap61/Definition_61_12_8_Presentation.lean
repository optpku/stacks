/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation

/-!
# Presentation bridge for Definition 61.12.8
-/

@[expose] public section

universe u v

/- Definition 61.12.8 -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigTopology :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigProetaleSite.bigSite X S))

/- Definition 61.12.8 -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallTopology :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigProetaleSite.smallSite X S))

/- Definition 61.12.8 -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.mem_smallPrecoverage_iff :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) →
      (S : X.carrier) →
        {U : AlgebraicGeometry.ChosenBigProetaleSite.smallSite X S} →
          {R : CategoryTheory.Presieve U} →
            R ∈ AlgebraicGeometry.ChosenBigProetaleSite.smallPrecoverage X S U ↔
              CategoryTheory.Presieve.overEquiv U.obj
                (R.map (AlgebraicGeometry.ChosenBigProetaleSite.smallInclusion X S)) ∈
                  X.pretopology U.obj.left)
