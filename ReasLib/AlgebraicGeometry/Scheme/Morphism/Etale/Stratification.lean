/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Stratification.Partition
public import ReasLib.AlgebraicGeometry.Scheme.LocallyClosedReduction
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.Constructible

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A quasi-compact and quasi-separated étale morphism admits a constructible locally closed
partition of its target whose reduced locally closed base changes are finite étale. -/
@[stacks 03S0]
theorem exists_constructiblePartition_finiteEtale_baseChange
    {U X : Scheme.{u}} (f : U ⟶ X)
    [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace X] [QuasiSeparatedSpace X] [Etale f] :
    ∃ Q : LocallyClosedPartition X,
      ∀ s : Q.toSet,
        Topology.IsConstructible (s : Set X) ∧
          let T : LocallyCloseds X :=
            ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
          IsFinite (pullback.snd f (Scheme.LocallyClosedReduction.ι T)) ∧
            Etale (pullback.snd f (Scheme.LocallyClosedReduction.ι T)) := sorry

end AlgebraicGeometry.Scheme.Hom
