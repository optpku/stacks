/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local compactness bridges

Small bridges between Mathlib's local compactness classes. The principal result
uses the natural `R1Space` hypothesis; Hausdorff spaces obtain it by instance
search.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.13.2 (`08ZR`), generalized to `R1Space`: weak local compactness
and local compactness agree in an `R₁` space. -/
@[stacks 08ZR "weak local compactness in R₁ spaces"]
theorem locallyCompactSpace_iff_weaklyLocallyCompactSpace [R1Space X] :
    LocallyCompactSpace X ↔ WeaklyLocallyCompactSpace X := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    infer_instance
