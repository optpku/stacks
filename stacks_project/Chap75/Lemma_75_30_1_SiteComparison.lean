/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.SiteComparison

universe u

/- Lemma 75.30.1: the canonical affine étale derived equivalence. -/
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.affineEtaleEquivalence :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.RLinear.TriangulatedEquivalence ℤ
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X)
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.AffineEtale X))
