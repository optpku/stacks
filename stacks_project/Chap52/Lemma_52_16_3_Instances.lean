/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap52.Situation_52_16_1
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open

open AlgebraicGeometry
universe u

/- Open restrictions of Noetherian schemes use the existing generic instance. -/
#check (AlgebraicGeometry.Scheme.instIsNoetherianRestrictOfIsNoetherian :
  {X : Scheme.{u}} → [IsNoetherian X] → (U : X.Opens) →
    IsNoetherian (X.restrict U.isOpenEmbedding))
