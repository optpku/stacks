/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.ExtremallyDisconnected
public import ReasLib.Topology.Maps.Minimal

/-!
# Minimal surjections onto extremally disconnected spaces
-/

@[expose] public section

universe u v

namespace ExtremallyDisconnected

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [ExtremallyDisconnected Y] {f : X → Y}

/-- A continuous minimal surjection from a compact Hausdorff space onto an extremally disconnected
Hausdorff space is a homeomorphism. -/
@[stacks 08YL "minimal surjections onto extremally disconnected spaces"]
theorem isHomeomorph_of_minimalSurjective
    (hf : Continuous f) (hminimal : IsMinimalSurjective f) :
    IsHomeomorph f := sorry

end ExtremallyDisconnected
