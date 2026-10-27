/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Rank.Generic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition (0HAF). For a quasi-coherent module F on an integral scheme X,
the rank is the cardinal dimension of its generic stalk F_η over κ(η),
represented here by X.functionField. The canonical definition also applies
without quasi-coherence. -/
@[stacks 0HAF] #check (AlgebraicGeometry.Scheme.Modules.genericRank :
  ∀ {X : Scheme.{u}} [IsIntegral X], X.Modules → Cardinal.{u})
