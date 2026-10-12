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

/- Domain-style sampling for Lemma 20.41.5:
- primary domain: tensor-to-iterated-internal-Hom comparison for cochain complexes of
  `𝒪_X`-modules on a ringed space;
- inspected owner declarations:
  `(ihom K).obj L`,
  `CategoryTheory.MonoidalClosed.Source.Iterated.map`;
- best owner abstraction:
  `CategoryTheory.MonoidalClosed.Source.Iterated.map`, with the iterated internal-Hom target
  expressed directly in the ambient braided closed category;
- primitive data:
  the three complexes `K`, `L`, `M` and the ambient monoidal-closed structure on the module
  category;
- derived API:
  the canonical comparison morphism together with its tensor-side uncurrying formula.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.5 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: the generic braided closed owner
  `CategoryTheory.MonoidalClosed.Source.Iterated.map`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file therefore stays at the `bridge/view` layer and directly recalls the generic owner,
without importing a chapter-level ringed-site specialization. -/

/- Lemma 20.41.5: given complexes `𝒦^•`, `𝓛^•`, and
`𝓜^•` of `𝒪_X`-modules on a ringed space `(X, 𝒪_X)`, there is a
canonical morphism
`Tot (Hom^•(𝓛^•, 𝓜^•) ⊗_{𝒪_X} 𝒦^•) ⟶ Hom^•(Hom^•(𝒦^•, 𝓛^•), 𝓜^•)`
of complexes of `𝒪_X`-modules. In the project API this is the generic
tensor-to-iterated-internal-Hom comparison, specialized to the canonical site of opens of `X`. -/
#check @CategoryTheory.MonoidalClosed.Source.Iterated.map

/- Specialized check for Lemma 20.41.5 on complexes of `𝒪_X`-modules. -/
@[stacks 0A8P]
#check
  (CategoryTheory.MonoidalClosed.Source.Iterated.map :
    ∀ K L M : CochainComplex X.Modules ℤ, (L ⟹ M) ⊗ K ⟶ ((K ⟹ L) ⟹ M))

/- Companion recall: uncurrying the canonical tensor-to-iterated-internal-Hom comparison
recovers the tensor-side composition/evaluation composite exposed by the generic owner theorem
below. -/
#check @CategoryTheory.MonoidalClosed.Source.Iterated.map_uncurry

end

end AlgebraicGeometry.RingedSpace
