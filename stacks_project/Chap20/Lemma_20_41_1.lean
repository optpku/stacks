/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.41.1:
- primary domain: internal-Hom complexes and tensor-Hom currying for cochain complexes of
  `𝒪_X`-modules;
- inspected owner declarations:
  `MonoidalClosed.internalHomTensorIso`,
  `K ⟹ L`,
  the standard closed-monoidal notation `K ⟹ L`;
- best owner abstraction:
  the canonical owner is `MonoidalClosed.internalHomTensorIso`, displayed here on the ringed-space
  complex category `CpxX` through the standard internal-Hom notation `K ⟹ L`;
- primitive data:
  the ambient ringed site and the three cochain complexes;
- derived API:
  the source-facing ringed-space specialization of the currying isomorphism.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.1 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: `MonoidalClosed.internalHomTensorIso`;
- `bridge/view`: the opens-site specialization, restated directly on
  `CochainComplex (X.Modules) ℤ`.

The target file therefore belongs at the `bridge/view` layer and should directly reuse the
Chapter 18 closed-monoidal owner theorem instead of rebuilding a parallel ringed-space
internal-Hom complex, its differential, or an extra wrapper isomorphism locally. -/

/- Lemma 20.41.1: for cochain complexes `𝒦^•`, `𝓛^•`, and `𝓜^•` of `𝒪_X`-modules on a ringed
space `(X, 𝒪_X)`, the iterated internal-Hom complex `𝒦^• ⟹ (𝓛^• ⟹ 𝓜^•)` is canonically
isomorphic to the internal-Hom complex `((𝒦^• ⊗ 𝓛^•) ⟹ 𝓜^•)`. In the project API this is the
generic owner theorem `MonoidalClosed.internalHomTensorIso`, specialized to the ringed-space
complex category `CpxX` coming from the canonical site of opens of `X`. -/
#check @CategoryTheory.MonoidalClosed.internalHomTensorIso

/- Specialized check for Lemma 20.41.1 on cochain complexes of `𝒪_X`-modules. -/
@[stacks 0A8M "internal-Hom tensor currying"]
#check
  (internalHomTensorIso :
    ∀ K L M : CochainComplex (X.Modules) ℤ,
      (ihom K).obj ((ihom L).obj M) ≅ (ihom (K ⊗ L)).obj M)

end

end AlgebraicGeometry.RingedSpace
