/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.ExtremallyDisconnected

/-!
# Projectivity characterizations of extremally disconnected compact Hausdorff spaces
-/

@[expose] public section

universe u

open Function

namespace CompactT2

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Projectivity of a compact Hausdorff space is equivalent to the existence of continuous sections
for all continuous surjections onto it from compact Hausdorff spaces. -/
@[stacks 08YN "projectivity by sections of compact Hausdorff surjections"]
theorem projective_iff_surjective_hasSection :
    CompactT2.Projective X ↔
      ∀ {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {f : Y → X},
        Continuous f → Surjective f → ∃ s : X → Y, Continuous s ∧ RightInverse s f := sorry

/-- Extremal disconnectedness, splitting of compact Hausdorff surjections, and compact-Hausdorff
projectivity are equivalent. -/
@[stacks 08YN "Gleason projectivity characterization"]
theorem extremallyDisconnected_section_projective_tfae :
    List.TFAE
      [ ExtremallyDisconnected X,
        ∀ {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {f : Y → X},
          Continuous f → Surjective f →
            ∃ s : X → Y, Continuous s ∧ RightInverse s f,
        CompactT2.Projective X ] := sorry

end CompactT2
