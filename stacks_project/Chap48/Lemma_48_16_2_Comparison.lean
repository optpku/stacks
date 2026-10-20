/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- The chapter-facing compatibility surface uses the reusable upper-shriek construction. -/
#check
  (AlgebraicGeometry.Scheme.Compactification.Of.upperShriek :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [IsNoetherian S]
      {X Y : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
      (P : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left
        (Over.mk f.hom.left))
      (aPlus : AlgebraicGeometry.Scheme.DerivedQCoh.Plus Y.obj.left ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh.Plus P.obj.right.left),
      AlgebraicGeometry.Scheme.DerivedQCoh.Plus Y.obj.left ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh.Plus X.obj.left)
