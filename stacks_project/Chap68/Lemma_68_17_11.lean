/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Decent
import StacksCheckRecall

/-!
# Valuative criterion for universal closedness of decent morphisms

A quasi-compact decent morphism of algebraic spaces is universally closed if
and only if it satisfies the existence part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.17.11: Let `f : X ⟶ Y` be a quasi-compact and decent morphism of
algebraic spaces over a scheme `S`. (For example if `f` is representable, or
quasi-separated, see Lemma 68.17.2.) Then `f` is universally closed if and only
if the existence part of the valuative criterion holds. -/
@[stacks 03M6] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.iff_existence_of_decent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [Decent f],
      UniversallyClosed f ↔ ValuativeCriterion.Existence f)

#check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence.of_universallyClosed_of_decent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [Decent f] [UniversallyClosed f],
      ValuativeCriterion.Existence f)
