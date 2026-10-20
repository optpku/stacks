/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.Constructible
import StacksCheckRecall

@[expose] public section

open Topology

universe u

/- Lemma 29.22.4: a locally constructible subset containing every generalization of a point
is a neighborhood of that point. -/
@[stacks 05LW] #check
  (AlgebraicGeometry.Scheme.IsLocallyConstructible.mem_nhds_of_generizations_subset :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {E : Set X} {x : X},
      IsLocallyConstructible E → {x' : X | x' ⤳ x} ⊆ E → E ∈ 𝓝 x)
