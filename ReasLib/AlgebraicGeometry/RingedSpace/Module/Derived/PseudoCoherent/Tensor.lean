/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pseudo-coherent closure under derived tensor

The ringed-space statement is a thin specialization of the shared pseudo-coherent predicate.  The
only tensor-construction input exposed to consumers is the canonical fixed-right derivability gate.
-/

open AlgebraicGeometry CategoryTheory
open scoped RingedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- Stacks 09J3 (1): pseudo-coherence bounds add under the canonical derived tensor product. -/
@[stacks 09J3 "ringed-space m-pseudo-coherent tensor closure"]
theorem IsMPseudoCoherent.tensor
    {K L : ModuleDerived X} {n m a b : ℤ}
    (hK : IsMPseudoCoherent K n) (hKLE : K.IsLE a)
    (hL : IsMPseudoCoherent L m) (hLLE : L.IsLE b) :
    IsMPseudoCoherent (K ⊗^L L) (max (m + a) (n + b)) := sorry

/-- Stacks 09J3 (2): pseudo-coherent derived modules are closed under derived tensor. -/
@[stacks 09J3 "ringed-space pseudo-coherent tensor closure"]
theorem IsPseudoCoherent.tensor
    {K L : ModuleDerived X}
    (hK : IsPseudoCoherent K) (hL : IsPseudoCoherent L) :
    IsPseudoCoherent (K ⊗^L L) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived

end
