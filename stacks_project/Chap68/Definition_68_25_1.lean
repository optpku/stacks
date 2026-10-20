/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Catenary
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 68.25.1: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
We say `X` is catenary if `|X|` is catenary (Topology, Definition 5.11.4 / `CatenarySpace`).
The general predicate on algebraic spaces specializes to this definition for decent spaces. -/
@[stacks 0ED4] #check (AlgebraicGeometry.AlgebraicSpace.IsCatenary :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isCatenary_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.IsCatenary X ↔
      TopologicalSpace.CatenarySpace (AlgebraicGeometry.AlgebraicSpace.Points X))
