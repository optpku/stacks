/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit preimmersion bridges

Mathlib owns `IsPreimmersion` and its canonical `Mono` instance. This leaf exposes the same
implication when the preimmersion certificate is supplied explicitly.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An explicit preimmersion certificate determines the canonical monomorphism property. -/
@[stacks 01L9 "preimmersion implies monomorphism"]
theorem IsPreimmersion.mono {X Y : Scheme.{u}} {f : X ⟶ Y}
    (h : IsPreimmersion f) : Mono f := sorry

end AlgebraicGeometry
