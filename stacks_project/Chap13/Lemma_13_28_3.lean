/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.K0
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.28.3:
- primary domain: triangulated Grothendieck groups and exact-functor functoriality;
- sampled owner declarations:
  `CategoryTheory.TriangulatedK0.lift`,
  `CategoryTheory.TriangulatedK0.lift_of`,
  `CategoryTheory.TriangulatedK0.map`,
  `CategoryTheory.TriangulatedK0.map_of`;
- source/core/bridge triage:
  `source-facing`: the exact-functoriality map on triangulated `K₀`;
  `core/canonical`: `CategoryTheory.TriangulatedK0.map`;
  `bridge/view`: `CategoryTheory.TriangulatedK0.map_of`, which evaluates the owner map on
    classes.

Primitive data are only the exact functor and the fact that it preserves distinguished triangles.
The quotient descent along `TriangulatedK0.lift` and its evaluation formula `lift_of` are derived
owner API from `ReasLib.CategoryTheory.Pretriangulated.K0`, so this file checks the existing
owner instead of reintroducing a parallel local map. -/

/- Lemma 13.28.3: the induced map on triangulated Grothendieck groups is the owner declaration
`CategoryTheory.TriangulatedK0.map`. -/
@[stacks 0FCQ] #check @TriangulatedK0.map

/- Companion check: the owner evaluation theorem on classes is
`CategoryTheory.TriangulatedK0.map_of`. -/
@[stacks 0FCQ] #check @TriangulatedK0.map_of

end CategoryTheory
