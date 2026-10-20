/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.4:
- primary domain: the tensor-internal-Hom unit for cochain complexes of `𝒪_X`-modules on a
  ringed space;
- inspected owner declarations:
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_spec`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_left`,
  `CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_right`;
- best owner abstraction:
  the generic categorical owner `CategoryTheory.MonoidalClosed.tensorInternalHomUnit`, with its
  companion specification and naturality theorems as derived API;
- primitive data:
  the ambient ringed space `X` and the two cochain complexes `K` and `L`;
- derived API:
  the assembled canonical morphism
  `K ⟶ L ⟹ (K ⊗ L)` and its left/right
  naturality laws.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.4 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: `CategoryTheory.MonoidalClosed.tensorInternalHomUnit`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the generic owner
and its companion theorems, rather than rebuilding a parallel ringed-space construction. -/

section

variable {X : RingedSpace.{u}}

/- Lemma 20.41.4: for complexes `K` and `L` of `𝒪_X`-modules on a ringed space `X`, there is a
canonical morphism `K ⟶ L ⟹ (K ⊗ L)`. In the project API this is the generic tensor-Hom unit,
specialized to cochain complexes of `𝒪_X`-modules on `X`. -/
#check @CategoryTheory.MonoidalClosed.tensorInternalHomUnit

/- Specialized check for Lemma 20.41.4 on cochain complexes of `𝒪_X`-modules. -/
@[stacks 0A8Q "tensor-internal-Hom unit"]
#check
  (tensorInternalHomUnit :
    ∀ K L : CochainComplex X.Modules ℤ, K ⟶ L ⟹ (K ⊗ L))

/- Companion recall: the coevaluation-plus-braiding formula for the canonical tensor-Hom unit is
the specialized form of the generic theorem below. -/
#check @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_spec

/- Companion recall: functoriality of the canonical tensor-Hom unit in the left complex is the
specialized form of the generic naturality theorem below. -/
#check @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_left

/- Companion recall: functoriality of the canonical tensor-Hom unit in the right complex is the
specialized form of the generic naturality theorem below. -/
#check @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_right

end

end AlgebraicGeometry.RingedSpace
