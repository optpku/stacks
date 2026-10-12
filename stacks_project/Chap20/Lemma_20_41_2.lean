/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.Algebra.Homology.HomologicalComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.Source

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

/- Domain-style sampling for Lemma 20.41.2:
- primary domain: composition pairing for internal-Hom complexes of `𝒪_X`-module cochain
  complexes;
- inspected owner declarations:
  `CategoryTheory.MonoidalClosed.Source.comp`,
  `(ihom K).obj L`,
  `HomologicalComplex.tensorObj`;
- best owner abstraction:
  `CategoryTheory.MonoidalClosed.Source.comp`, whose source is already the canonical tensor
  product of the two internal-Hom objects in source order;
- primitive data:
  the ambient ringed site and the three cochain complexes;
- derived API:
  the assembled composition morphism and its degreewise formula.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.2 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: the generic braided closed owner
  `CategoryTheory.MonoidalClosed.Source.comp`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file therefore stays at the `bridge/view` layer and directly recalls the generic owner
instead of importing a chapter-level ringed-site specialization. -/

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/- Lemma 20.41.2: for a ringed space `(X, 𝒪_X)` and complexes `K`, `L`, and `M` of
`𝒪_X`-modules, there is a canonical morphism
`Tot (ℋom^•(L, M) ⊗[𝒪_X] ℋom^•(K, L)) ⟶ ℋom^•(K, M)`.
This is the generic source-order composition morphism specialized to the site of opens of `X`. -/
#check @CategoryTheory.MonoidalClosed.Source.comp

/- Specialized check for Lemma 20.41.2 on complexes of `𝒪_X`-modules. -/
@[stacks 0A8N]
#check
  (CategoryTheory.MonoidalClosed.Source.comp :
    ∀ K L M : CochainComplex X.Modules ℤ, (L ⟹ M) ⊗ (K ⟹ L) ⟶ (K ⟹ M))

end

end AlgebraicGeometry.RingedSpace
