/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DenseRange
import StacksCheckRecall

/-!
# Refined valuative criterion for universal closedness

A quasi-compact morphism of algebraic spaces that satisfies uniqueness and
existence of the valuative criterion along a quasi-compact dominant morphism is
universally closed, and is separated if it is moreover quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.42.5: The restricted valuative criterion along a quasi-compact
morphism with dense image implies universal closedness, and also separatedness
when the given morphism is quasi-separated. -/
@[stacks 089G] #check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Along.universallyClosed :
    ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
      (f : X ⟶ Y) (h : U ⟶ X),
      [QuasiCompact f] → [QuasiCompact h] → [Dominant h] →
      ValuativeCriterion.Along.Uniqueness h f → ValuativeCriterion.Along.Existence h f →
      UniversallyClosed f)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Along.separated :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (h : U ⟶ X),
    [QuasiCompact f] → [QuasiCompact h] → [Dominant h] → [QuasiSeparated f] →
    ValuativeCriterion.Along.Uniqueness h f → ValuativeCriterion.Along.Existence h f →
    Separated f)
