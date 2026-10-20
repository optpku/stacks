/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Fixed-right view of ringed-space derived tensor

The two-variable derived tensor of `𝒪_X`-modules remains a left-derived model after fixing its
right argument.  Registering this canonical compatibility once avoids proof-local instances in
every Tor comparison.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor

variable {X : RingedSpace.{u}}
variable [Has X]

/-- The bifunctorial derived tensor is compatible with fixed-right derivation. -/
@[stacks 06YH "ringed-space fixed-right derived tensor compatibility", instance]
noncomputable instance rightCompatible (L : ModuleDerived X) :
    DerivedCategory.DerivedTensor.Bifunctor.Right.Compatible L := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor

end
