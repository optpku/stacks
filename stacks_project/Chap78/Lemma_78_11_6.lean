/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.BaseChange
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 78.11.6 (1): base change along `f : B' ⟶ B` sends a groupoid in algebraic spaces
over `B` to a groupoid in algebraic spaces over `B'`. -/
@[stacks 0DTA] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.baseChange :
  {S : AlgebraicGeometry.Scheme.{u}} → {B B' : AlgebraicGeometry.AlgebraicSpace S} →
    (B' ⟶ B) → AlgebraicGeometry.GroupoidAlgebraicSpace B →
      AlgebraicGeometry.GroupoidAlgebraicSpace B')

/- Lemma 78.11.6 (2): after transporting the base-changed groupoid back over `B` via
`Over.map f`, the canonical object and arrow projections form a morphism of groupoids in
algebraic spaces. -/
@[stacks 0DTA] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.baseChangeProjection :
  {S : AlgebraicGeometry.Scheme.{u}} → {B B' : AlgebraicGeometry.AlgebraicSpace S} →
    (f : B' ⟶ B) → (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
        (AlgebraicGeometry.GroupoidAlgebraicSpace.changeBase f
          (AlgebraicGeometry.GroupoidAlgebraicSpace.baseChange f G)) G)
