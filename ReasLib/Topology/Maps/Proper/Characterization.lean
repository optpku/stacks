/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.TFAE
public import ReasLib.Topology.Maps.Proper.QuasiProper

/-!
# Proper-Map Characterizations

The source's four standard formulations are bundled only as a `List.TFAE`;
the individual equivalences remain in Mathlib and `QuasiProper`.
-/

@[expose] public section

open Set

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

namespace Continuous

/-- Theorem 5.17.5: for a continuous map, quasi-proper-and-closed,
`IsProperMap`, pullback closedness, and closedness with compact fibers are
equivalent. -/
@[stacks 005R]
theorem isProperMap_tfae (hf : Continuous f) :
    List.TFAE
      [ IsQuasiProperMap f ∧ IsClosedMap f,
        IsProperMap f,
        (∀ (Z : Type (max u v)) [TopologicalSpace Z] (g : Z → Y), Continuous g →
          IsClosedMap (@Function.Pullback.snd X Y Z f g)),
        IsClosedMap f ∧ ∀ y : Y, IsCompact (f ⁻¹' {y}) ] := sorry

end Continuous
