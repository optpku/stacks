/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [HasBinaryBiproducts 𝒜]

/- Domain-style sampling:
- primary domain: triangulated structures on homotopy categories of cochain complexes;
- sampled owner declarations:
  `K(𝒜)`;
  `Pretriangulated (K(𝒜))`;
  `IsTriangulated (K(𝒜))`;
- best owner abstraction: the canonical owner `IsTriangulated (K(𝒜))`;
- primitive data: an additive category with zero object and binary biproducts;
- derived API: the triangulated structure on the homotopy category of cochain complexes.

Source/core/bridge triage:
- `source-facing`: Proposition 13.10.3, asserting that the homotopy category `K(𝒜)` is
  triangulated;
- `core/canonical`: the existing triangulated owner instance on `K(𝒜)`;
- `bridge/view`: the textbook notation `K(𝒜)` from `Definition_13_8_1` for
  `HomotopyCategory 𝒜 (up ℤ)`.

This proposition is therefore a pure canonical recall item. The file should use the existing owner
instance directly, with no local wrapper or duplicate declaration.
-/

/- Proposition 13.10.3: for an additive category `𝒜`, the homotopy category
`K(𝒜)` of cochain complexes, equipped with its standard translation functors and
distinguished triangles, carries the canonical triangulated structure. This is exactly the
existing owner instance `IsTriangulated (K(𝒜))`. -/
@[stacks 014S] #check (inferInstance : IsTriangulated (K(𝒜)))

end CategoryTheory
