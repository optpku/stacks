/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import StacksCheckRecall

@[expose] public section

/- Domain-style sampling for Lemma 13.9.17:
- primary domain: mapping-cone triangles and triangles attached to degreewise split short
  complexes of cochain complexes;
- inspected owner declarations:
  `CochainComplex.mappingCone.triangle`,
  `CochainComplex.triangleOfDegreewiseSplit`,
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`,
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- best owner abstraction: the upstream mapping-cone owner comparison
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- primitive data: a morphism of cochain complexes `f : K^• ⟶ L^•`;
- derived API: the rotated standard mapping-cone triangle, the canonical degreewise split short
  complex `triangleRotateShortComplex f`, its degreewise splitting, and the resulting triangle
  comparison all remain upstream and are reused directly here.
-/

/- Source/core/bridge triage:
- `source-facing`: the textbook identification of the triangle
  `(L^•, C(f)^•, K^•[1], i, p, f[1])`;
- `core/canonical`: the cochain-level owner comparison
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`, using the rotated
  triangle `(L^•, C(f)^•, K^•[1], i, -p, -f[1])` and the short complex with maps `(i, -p)`;
- `bridge/view`: the Mathlib and Stacks triangles are isomorphic, not literally identical.
  The comparison has components `(𝟙 L^•, 𝟙 C(f)^•, -𝟙 K^•[1])`, i.e. `(1, 1, -1)`.
  This immediate sign comparison is recorded here; the numbered lemma remains a direct recall
  of the core owner without a new wrapper or bridge declaration.
-/

/- Lemma 13.9.17: for a morphism of cochain complexes `f : K^• ⟶ L^•` in an additive category,
Stacks uses the cone inclusion `i` and projection `p`, so the termwise split sequence with
maps `(i, p)` has associated triangle `(L^•, C(f)^•, K^•[1], i, p, f[1])`.
Mathlib's standard cone triangle has last map `-p`; its rotation has maps `(i, -p, -f[1])`.
The owner `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit` identifies
this rotation with the triangle associated to `triangleRotateShortComplex f`, whose maps
are `(i, -p)` and whose connecting map is `-f[1]`.
The isomorphism from this Mathlib triangle to the Stacks triangle has components
`(𝟙 L^•, 𝟙 C(f)^•, -𝟙 K^•[1])`: using minus the identity on the third object changes
both `-p` and `-f[1]` to the Stacks signs. Thus the recalled owner gives the categorical
reformulation with this immediate `(1, 1, -1)` sign comparison. -/
@[stacks 014O] #check @CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit
