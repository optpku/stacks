/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Stratification
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/- Lemma 59.72.1 -/
@[stacks 03S0]
#check (AlgebraicGeometry.Scheme.Hom.exists_constructiblePartition_finiteEtale_baseChange :
    ∀ {U X : Scheme.{u}} (f : U ⟶ X),
      [CompactSpace U] → [QuasiSeparatedSpace U] →
      [CompactSpace X] → [QuasiSeparatedSpace X] → [Etale f] →
      ∃ Q : LocallyClosedPartition X,
        ∀ s : Q.toSet,
          Topology.IsConstructible (s : Set X) ∧
            let T : LocallyCloseds X :=
              ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
            IsFinite (pullback.snd f (Scheme.LocallyClosedReduction.ι T)) ∧
              Etale (pullback.snd f (Scheme.LocallyClosedReduction.ι T)))
