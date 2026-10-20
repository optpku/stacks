/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Smooth

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 40.10.13 (1): if the object scheme of a groupoid scheme is the spectrum of a
perfect field, its source and target maps are locally of finite type, and its arrow scheme is
reduced, then the source map is smooth. -/
@[stacks 04RB]
#check
  (AlgebraicGeometry.GroupoidScheme.sourceSmoothOfPerfectFieldOfIsReduced :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k] [PerfectField k]
      (eU : Spec (CommRingCat.of k) ≅ G.U.left)
      [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left] [IsReduced G.R.left],
      Smooth G.s.left)

/- Lemma 40.10.13 (2): if the object scheme of a groupoid scheme is the spectrum of a
perfect field, its source and target maps are locally of finite type, and its arrow scheme is
reduced, then the target map is smooth. -/
@[stacks 04RB]
#check
  (AlgebraicGeometry.GroupoidScheme.targetSmoothOfPerfectFieldOfIsReduced :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k] [PerfectField k]
      (eU : Spec (CommRingCat.of k) ≅ G.U.left)
      [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left] [IsReduced G.R.left],
      Smooth G.t.left)

end AlgebraicGeometry.GroupoidScheme
