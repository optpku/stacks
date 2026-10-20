/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.StrongSplitting
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Situation 79.15.2 (Strong splitting): standing hypotheses for a pointed groupoid scheme. -/
@[stacks 04RL] #check (AlgebraicGeometry.GroupoidScheme.StrongSplitting :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left), Prop)

#check (AlgebraicGeometry.GroupoidScheme.StrongSplitting.iff :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left),
    StrongSplitting G point ↔
      IsSeparated G.s.left ∧ IsSeparated G.t.left ∧
        LocallyOfFiniteType G.s.left ∧ LocallyOfFiniteType G.t.left ∧
          (loopPoints G point).Finite ∧
            ∀ arrow ∈ loopPoints G point,
              Scheme.Hom.FiniteType.QuasiFiniteAt G.s.left arrow)

#check (AlgebraicGeometry.GroupoidScheme.StrongSplitting.of_finite_sourceFiber :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left),
    [IsSeparated G.s.left] → [IsSeparated G.t.left] →
    [LocallyOfFiniteType G.s.left] → [LocallyOfFiniteType G.t.left] →
    Set.Finite (G.s.left ⁻¹' ({point} : Set G.U.left)) → StrongSplitting G point)

end AlgebraicGeometry.GroupoidScheme
