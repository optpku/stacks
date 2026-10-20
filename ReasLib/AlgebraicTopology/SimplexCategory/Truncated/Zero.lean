/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The zero-truncated simplex category

The zero-truncated simplex category has one simplex up to a canonical isomorphism.  This file
keeps that fact concrete: both directions are the explicit constant monotone maps, so downstream
functor-category constructions do not depend on an opaque equality transport or a chosen witness.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial SimplexCategory.Truncated

namespace SimplexCategory.Truncated

/-- The canonical morphism from the zero simplex to an object of the zero-truncated simplex
category. -/
@[stacks 0182 "map from the zero simplex in the zero-truncated simplex category"]
def fromZero (Delta : SimplexCategory.Truncated 0) :
    (⦋0⦌₀ : SimplexCategory.Truncated 0) ⟶ Delta :=
  ObjectProperty.homMk (SimplexCategory.const ⦋0⦌ Delta.obj 0)

/-- The canonical morphism from an object of the zero-truncated simplex category to the zero
simplex. -/
@[stacks 0182 "map to the zero simplex in the zero-truncated simplex category"]
def toZero (Delta : SimplexCategory.Truncated 0) :
    Delta ⟶ (⦋0⦌₀ : SimplexCategory.Truncated 0) :=
  ObjectProperty.homMk (SimplexCategory.const Delta.obj ⦋0⦌ 0)

/-- The two canonical zero-truncated simplex maps compose to the identity of the zero simplex. -/
@[simp, stacks 0182 "zero-truncated simplex comparison at zero"]
theorem fromZero_toZero (Delta : SimplexCategory.Truncated 0) :
    fromZero Delta ≫ toZero Delta = 𝟙 (⦋0⦌₀ : SimplexCategory.Truncated 0) := sorry

/-- The two canonical zero-truncated simplex maps compose to the identity of the given object. -/
@[simp, stacks 0182 "zero-truncated simplex comparison at an object"]
theorem toZero_fromZero (Delta : SimplexCategory.Truncated 0) :
    toZero Delta ≫ fromZero Delta = 𝟙 Delta := sorry

/-- Every object of the zero-truncated simplex category is canonically isomorphic to its unique
zero simplex.  The morphism data consists of the explicit constant monotone maps. -/
@[stacks 0182 "canonical zero-truncated simplex isomorphism"]
def zeroIso (Delta : SimplexCategory.Truncated 0) :
    (⦋0⦌₀ : SimplexCategory.Truncated 0) ≅ Delta where
  hom := fromZero Delta
  inv := toZero Delta
  hom_inv_id := fromZero_toZero Delta
  inv_hom_id := toZero_fromZero Delta

/-- The forward map of the canonical zero-truncated simplex isomorphism is `fromZero`. -/
@[simp, stacks 0182 "forward canonical zero-truncated simplex map"]
theorem zeroIso_hom (Delta : SimplexCategory.Truncated 0) :
    (zeroIso Delta).hom = fromZero Delta := sorry

/-- The inverse map of the canonical zero-truncated simplex isomorphism is `toZero`. -/
@[simp, stacks 0182 "inverse canonical zero-truncated simplex map"]
theorem zeroIso_inv (Delta : SimplexCategory.Truncated 0) :
    (zeroIso Delta).inv = toZero Delta := sorry

end SimplexCategory.Truncated
