/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction

open CategoryTheory AlgebraicGeometry

universe u

/- The restricted groupoid and its canonical projection are defined over the same base. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.pullback :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} →
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
        AlgebraicGeometry.GroupoidAlgebraicSpace B)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} →
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
        AlgebraicGeometry.GroupoidAlgebraicSpace.Hom (G.pullback g) G)
