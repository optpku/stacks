/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReasLib.RingTheory.Smooth.Topological
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Adic Formal Smoothness

@stack 07EE
@stack 07NI
-/

open scoped Topology

universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

/-- Definition 15.37.3: a ring homomorphism is formally smooth for the target `𝔫`-adic topology
when it is topologically formally smooth from the discrete source topology. -/
@[stacks 07NI "adic formal smoothness"]
abbrev formally_smooth_for_adic (f : R →+* S) (𝔫 : Ideal S) : Prop :=
  letI : TopologicalSpace R := ⊥
  letI : TopologicalSpace S := Ideal.adicTopology 𝔫
  FormallySmoothTopologically.{u, v, max u v} f

/-- The adic formal-smoothness predicate unfolds to topological formal smoothness with a discrete
source and the target adic topology. -/
theorem formally_smooth_for_adic_iff (f : R →+* S) (𝔫 : Ideal S) :
    formally_smooth_for_adic f 𝔫 ↔
      (letI : TopologicalSpace R := ⊥
       letI : TopologicalSpace S := Ideal.adicTopology 𝔫
       FormallySmoothTopologically.{u, v, max u v} f) := sorry

/-- Adic formal smoothness persists when the target defining ideal is enlarged. -/
@[stacks 07EE "monotonicity of adic formal smoothness"]
theorem formally_smooth_for_adic_of_le (f : R →+* S) {𝔫 𝔫' : Ideal S} (h𝔫 : 𝔫 ≤ 𝔫')
    (hf : formally_smooth_for_adic f 𝔫) : formally_smooth_for_adic f 𝔫' := sorry

end

end RingHom
