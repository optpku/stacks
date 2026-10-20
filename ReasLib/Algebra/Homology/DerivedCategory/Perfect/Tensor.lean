/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness under derived tensor product

@stack 0GM0

Perfect objects of a derived module category are closed under the canonical fixed-right derived
tensor product.  The owner uses `DerivedTensor.Right.obj` directly, without requiring an ambient
monoidal instance on the whole derived category.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R]

/-- Lemma 15.75.11 (Stacks `0GM0`): the derived tensor product of perfect objects is perfect. -/
@[stacks 0GM0 "perfectness under derived tensor product"]
theorem IsPerfect.tensor
    {K L : DerivedCategory (ModuleCat R)} (hK : K.IsPerfect) (hL : L.IsPerfect) :
    DerivedCategory.IsPerfect (DerivedTensor.Right.obj K L) := sorry

end CategoryTheory.DerivedCategory
