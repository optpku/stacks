/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantOpen

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 39.19.4: under quasi-compactness and flatness of both structure maps and
quasi-separatedness of the object scheme, every compact open lies inside an invariant open
that lies inside a compact open. -/
@[stacks 0APB] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantOpen_between :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [QuasiCompact G.s.left] [Flat G.s.left] [QuasiCompact G.t.left] [Flat G.t.left]
      [QuasiSeparatedSpace G.U.left] (W : CompactOpens G.U.left),
      ∃ (V : Opens G.U.left) (W' : CompactOpens G.U.left),
        G.toPreRelation.IsOpenInvariant V ∧ W.toOpens ≤ V ∧ V ≤ W'.toOpens)

end AlgebraicGeometry.GroupoidScheme
