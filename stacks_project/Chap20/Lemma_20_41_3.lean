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

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.41.3:
- primary domain: tensor-internal-Hom comparison for cochain complexes of module sheaves;
- inspected owner declarations:
  `(ihom M).obj L`,
  `CategoryTheory.MonoidalClosed.Source.tensor`;
- best owner abstraction:
  `CategoryTheory.MonoidalClosed.Source.tensor`;
- primitive data:
  the ambient ringed site together with the three complexes;
- derived API:
  the canonical internal-Hom complex and the assembled tensor-internal-Hom comparison morphism.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.3 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: the generic braided closed owner
  `CategoryTheory.MonoidalClosed.Source.tensor`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file therefore stays at the `bridge/view` layer and directly recalls the generic owner,
without importing a chapter-level ringed-site specialization. -/

/- Lemma 20.41.3: for a ringed space `(X, 𝒪_X)` and complexes `𝒦^•`, `𝓛^•`, and `𝓜^•`
of `𝒪_X`-modules, there is a canonical morphism from
`Tot (𝒦^• ⊗_{𝒪_X} Hom^•(𝓜^•, 𝓛^•))` to
`Hom^•(𝓜^•, Tot (𝒦^• ⊗_{𝒪_X} 𝓛^•))`.
In the project API this is the generic source-order tensor/internal-Hom comparison morphism,
specialized to the canonical site of opens of `X`. -/
#check @CategoryTheory.MonoidalClosed.Source.tensor

/- Specialized check for Lemma 20.41.3 on complexes of `𝒪_X`-modules. -/
@[stacks 0BYR]
#check
  (CategoryTheory.MonoidalClosed.Source.tensor :
    ∀ K L M : CochainComplex X.Modules ℤ, K ⊗ (M ⟹ L) ⟶ (M ⟹ (K ⊗ L)))

/- Companion check: uncurrying the canonical tensor-internal-Hom comparison recovers the
braiding/evaluation composite already exposed by the generic owner theorem below. -/
#check @CategoryTheory.MonoidalClosed.Source.tensor_spec

end

end AlgebraicGeometry.RingedSpace
