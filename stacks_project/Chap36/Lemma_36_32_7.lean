/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.FiberSections
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 36.32.7: for a proper morphism of schemes, every idempotent global section on a
scheme-theoretic fiber lies in the range of the canonical map from the pushforward stalk. -/
@[stacks 0G7X] #check
  (AlgebraicGeometry.IsProper.idempotent_mem_range_fiberSections :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsProper f] (s : S)
      (e : AlgebraicGeometry.Scheme.globalSectionsRing (f.fiber s))
      (he : IsIdempotentElem e),
      e ∈ (AlgebraicGeometry.Scheme.Hom.FiberSections.pushforwardStalkMap f s).range)
