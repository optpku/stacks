/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

universe u

/- Definition 72.11.1 (1): geometric reducedness at a point is geometric reducedness
of the étale local rings over that point. -/
@[stacks 0DMQ] #check (AlgebraicGeometry.AlgebraicSpace.GeometricallyReducedAt :
  {k : Type u} → [Field k] → (X : AlgebraicSpace (Spec (of k))) →
    AlgebraicSpace.Points X → Prop)

/- Definition 72.11.1 (2): geometric reducedness over the field is geometric
reducedness at every point. -/
@[stacks 0DMQ] #check (AlgebraicGeometry.AlgebraicSpace.GeometricallyReduced.iff_forall_geometricallyReducedAt :
  {k : Type u} → [Field k] → (X : AlgebraicSpace (Spec (of k))) →
    (AlgebraicGeometry.AlgebraicSpace.GeometricallyReduced X ↔
      ∀ x : AlgebraicSpace.Points X,
        AlgebraicGeometry.AlgebraicSpace.GeometricallyReducedAt X x))
