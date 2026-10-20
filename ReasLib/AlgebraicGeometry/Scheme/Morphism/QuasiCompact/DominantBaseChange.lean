/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.Specialization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dominant base changes of quasi-compact morphisms

This file records a dominant base-change criterion along morphisms that lift generalizations.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A quasi-compact dominant morphism remains dominant after base change along a morphism whose
underlying map lifts generalizations. -/
@[stacks 0H3F]
theorem isDominant_pullbackSnd_of_isDominant_of_generalizingMap
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [QuasiCompact f] [IsDominant f]
    (hg : GeneralizingMap g.base) :
    IsDominant (pullback.snd f g) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨x, hx⟩ := f.exists_specializing_preimage (g y)
  obtain ⟨y', hy', hgy'⟩ := hg hx
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x y' hgy'.symm
  have hy'range : y' ∈ Set.range (pullback.snd f g).base := ⟨z, hz⟩
  exact (closure_mono (Set.singleton_subset_iff.mpr hy'range))
    (specializes_iff_mem_closure.mp hy')

end AlgebraicGeometry
