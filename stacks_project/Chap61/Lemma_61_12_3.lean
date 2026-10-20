/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Covering

@[expose] public section

universe u

/- Lemma 61.12.3 (1): Any étale covering is a pro-étale covering. -/
@[stacks 098B] #check
  (AlgebraicGeometry.Scheme.Proetale.etalePrecoverage_le_proetalePrecoverage :
    AlgebraicGeometry.Scheme.etalePrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.proetalePrecoverage.{u})

/- Lemma 61.12.3 (2): Any Zariski covering is a pro-étale covering. -/
@[stacks 098B] #check
  (AlgebraicGeometry.Scheme.Proetale.zariskiPrecoverage_le_proetalePrecoverage :
    AlgebraicGeometry.Scheme.zariskiPrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.proetalePrecoverage.{u})
