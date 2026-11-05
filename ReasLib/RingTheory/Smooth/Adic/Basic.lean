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
  -- Local instance justification (noncanonical choice): the adic predicate fixes the discrete
  -- source topology, independently of any other topology on the underlying ring.
  letI : TopologicalSpace R := ⊥
  -- Local instance justification (noncanonical choice): the target topology must be the one
  -- determined by the explicit ideal `𝔫`, which varies with the predicate argument.
  letI : TopologicalSpace S := Ideal.adicTopology 𝔫
  FormallySmoothTopologically.{u, v, max u v} f

/-- The adic formal-smoothness predicate unfolds to topological formal smoothness with a discrete
source and the target adic topology. -/
theorem formally_smooth_for_adic_iff (f : R →+* S) (𝔫 : Ideal S) :
    formally_smooth_for_adic f 𝔫 ↔
      (-- Local instance justification (noncanonical choice): pin the discrete source topology
       -- used in the definition being unfolded, rather than introducing a topology assumption.
       letI : TopologicalSpace R := ⊥
       -- Local instance justification (noncanonical choice): pin exactly the `𝔫`-adic target
       -- topology used by `formally_smooth_for_adic`.
       letI : TopologicalSpace S := Ideal.adicTopology 𝔫
       FormallySmoothTopologically.{u, v, max u v} f) := sorry

/-- Adic formal smoothness persists when the target defining ideal is enlarged. -/
@[stacks 07EE "monotonicity of adic formal smoothness"]
theorem formally_smooth_for_adic_of_le (f : R →+* S) {𝔫 𝔫' : Ideal S} (h𝔫 : 𝔫 ≤ 𝔫')
    (hf : formally_smooth_for_adic f 𝔫) : formally_smooth_for_adic f 𝔫' := sorry

end

end RingHom
