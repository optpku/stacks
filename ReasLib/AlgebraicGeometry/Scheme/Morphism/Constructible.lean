/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Constructible

@[expose] public section

open Topology

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The inverse image of a locally constructible subset under a morphism of schemes is locally
constructible. -/
@[stacks 054I "(2)"]
theorem isLocallyConstructible_preimage (f : X ⟶ Y) {E : Set Y}
    (hE : IsLocallyConstructible E) :
    IsLocallyConstructible (f ⁻¹' E) := sorry

end AlgebraicGeometry.Scheme.Hom
