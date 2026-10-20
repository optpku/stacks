/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Representable
import StacksCheckRecall

/-!
# Representable morphisms and the existence part of the valuative criterion

For a representable morphism of algebraic spaces, the existence part of the
valuative criterion is equivalent to the scheme-style existence of a dotted
arrow in every valuative square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.41.2
Let `S` be a scheme, and let `f : X ⟶ Y` be a representable morphism of
algebraic spaces over `S`. Its existence criterion using dominating valuation
ring extensions is equivalent to the existence of a lift over the original
valuation ring in every valuative square.
-/
@[stacks 03K8] #check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence.iff_hasLift :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
    yoneda.relativelyRepresentable f →
      (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence f ↔
        ∀ sq : AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq f,
          sq.commSq.HasLift))

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence.of_hasLift :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
    (∀ sq : AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq f,
      sq.commSq.HasLift) →
      AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence f)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence.hasLift :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
    yoneda.relativelyRepresentable f →
      [AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence f] →
        (sq : AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq f) →
          sq.commSq.HasLift)
