/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.UniversallyClosed
import StacksCheckRecall

/-!
# Valuative criterion for universal closedness

A quasi-separated universally closed morphism of algebraic spaces satisfies the
existence part of the valuative criterion. Under quasi-compactness and
quasi-separatedness, universal closedness is equivalent to existence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.42.2 (1): A quasi-separated universally closed morphism satisfies
the existence part of the valuative criterion. -/
@[stacks 0A3X] #check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence.of_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [QuasiSeparated f] → [UniversallyClosed f] → ValuativeCriterion.Existence f)

/- Lemma 67.42.2 (2): For a quasi-compact quasi-separated morphism, universal
closedness is equivalent to the existence part of the valuative criterion. -/
@[stacks 0A3X] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.iff_existence :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [QuasiCompact f] → [QuasiSeparated f] →
      (UniversallyClosed f ↔ ValuativeCriterion.Existence f))
