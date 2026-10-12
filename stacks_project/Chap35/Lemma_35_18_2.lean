/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Smooth
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.18.2: normality of schemes is local for the smooth precoverage. -/
@[stacks 034F] #check
  (AlgebraicGeometry.Scheme.isNormal.smoothLocal :
    CategoryTheory.ObjectProperty.IsLocal
      (AlgebraicGeometry.Scheme.isNormal :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage)
