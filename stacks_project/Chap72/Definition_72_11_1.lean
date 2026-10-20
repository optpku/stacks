/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.11.1 (1): an algebraic space `X` over a field `k` is geometrically
reduced at a point `x` of `|X|` if the étale local ring `𝒪_{X, x̄}` is geometrically
reduced over `k`. -/
@[stacks 0DMQ] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricallyReducedAt :
    {k : Type u} → [Field k] → (X : AlgebraicSpace (Spec (of k))) → Points X → Prop)

/- Definition 72.11.1 (2): an algebraic space `X` over a field `k` is geometrically
reduced over `k` if `X` is geometrically reduced at every point of `|X|`. -/
@[stacks 0DMQ] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricallyReduced.iff_forall_geometricallyReducedAt :
    {k : Type u} → [Field k] → (X : AlgebraicSpace (Spec (of k))) →
      (AlgebraicGeometry.AlgebraicSpace.GeometricallyReduced X ↔
        ∀ x : Points X, AlgebraicGeometry.AlgebraicSpace.GeometricallyReducedAt X x))
