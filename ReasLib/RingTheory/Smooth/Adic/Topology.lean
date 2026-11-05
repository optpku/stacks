/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.Adic.Basic
public import ReasLib.RingTheory.Topology.Adic.Continuity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Topological and adic formal smoothness

@stack 07EC
-/

@[expose] public section

open scoped Topology

universe u v

namespace RingHom

section AlgebraicToTopological

variable {R : Type u} {S : Type v}
variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
variable [CommRing S] [TopologicalSpace S] [TopologicalRing.IsPreadicRing S]

/-- Lemma 15.37.2 (1) (07EC): an algebraically formally smooth ring map is formally smooth for
any linear topology on the source and any pre-adic topology on the target for which the map is
continuous. -/
@[stacks 07EC "(1), algebraic formal smoothness implies topological formal smoothness"]
theorem FormallySmooth.toTopologically {f : R →+* S} (hf : f.FormallySmooth)
    (hcont : Continuous f) :
    f.FormallySmoothTopologically := sorry

end AlgebraicToTopological

section FormallyEtale

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A formally étale ring map is formally smooth for every adic topology on its target. -/
theorem FormallyEtale.formallySmoothForAdic {f : R →+* S} (hf : f.FormallyEtale)
    (𝔫 : Ideal S) : f.formally_smooth_for_adic 𝔫 := sorry

end FormallyEtale

section SourceTopology

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 15.37.2 (2) (07EC): for a map continuous between the `𝔪`-adic and `𝔫`-adic
topologies, formal smoothness is unchanged when the source topology is replaced by the discrete
topology. -/
@[stacks 07EC "(2), independence of the source adic topology"]
theorem formallySmoothTopologically_adicSource_iff_discreteSource
    (f : R →+* S) (𝔪 : Ideal R) (𝔫 : Ideal S)
    (hcont :
      -- Local instance justification (noncanonical choice): this hypothesis tests continuity
      -- for the source `𝔪`-adic topology which the conclusion compares with the discrete one.
      letI : TopologicalSpace R := 𝔪.adicTopology
      -- Local instance justification (noncanonical choice): continuity must use the same
      -- `𝔫`-adic target topology on both sides of the equivalence.
      letI : TopologicalSpace S := 𝔫.adicTopology
      Continuous f) :
    (-- Local instance justification (noncanonical choice): the left side specifically uses
     -- the `𝔪`-adic source topology; the right side uses the discrete source topology.
     letI : TopologicalSpace R := 𝔪.adicTopology
     -- Local instance justification (noncanonical choice): retain exactly the target topology
     -- from `hcont` and the right-hand adic formal-smoothness predicate.
     letI : TopologicalSpace S := 𝔫.adicTopology
     FormallySmoothTopologically.{u, v, max u v} f) ↔
      formally_smooth_for_adic f 𝔫 := sorry

end SourceTopology

end RingHom
