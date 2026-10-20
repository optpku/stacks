/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.FaceRelation
import StacksCheckRecall

/-!
# Lemma 85.30.1

A cartesian morphism of simplicial schemes over the Čech nerve of `f : X ⟶ S`
induces an equivalence relation on `Y _⦋0⦌` over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Simplicial
open Scheme.PreRelation

universe u

/- Lemma 85.30.1: a cartesian morphism to the Čech nerve of `f : X ⟶ S` makes
`j = (Y.δ 1, Y.δ 0)` an equivalence relation on `Y _⦋0⦌` over `S`. -/
@[stacks 024E]
#check
  (AlgebraicGeometry.Scheme.Hom.instIsEquivalenceRelation_facePreRelation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) {Y : SimplicialObject Scheme.{u}}
      (π : Y ⟶ f.simplicialScheme) [SimplicialObject.IsCartesian π],
      IsEquivalenceRelation
        (AlgebraicGeometry.Scheme.Hom.facePreRelation f π).t
        (AlgebraicGeometry.Scheme.Hom.facePreRelation f π).s)
