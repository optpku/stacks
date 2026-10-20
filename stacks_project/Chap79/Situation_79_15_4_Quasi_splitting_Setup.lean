/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuasiSplitting

universe u

#check (AlgebraicGeometry.GroupoidScheme.isQuasiSplittingSituation_iff :
  {S : AlgebraicGeometry.Scheme.{u}} →
    (G : AlgebraicGeometry.GroupoidScheme S) →
    (u : G.U.left) →
      AlgebraicGeometry.GroupoidScheme.IsQuasiSplittingSituation G u ↔
        AlgebraicGeometry.IsSeparated G.s.left ∧
          AlgebraicGeometry.IsSeparated G.t.left ∧
            AlgebraicGeometry.LocallyOfFiniteType G.s.left ∧
              AlgebraicGeometry.LocallyOfFiniteType G.t.left ∧
                G.s.left.QuasiFiniteAt (G.e.left u))
