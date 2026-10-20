/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.ValuativeCriterion
import StacksCheckRecall

/-!
# Valuative criterion for properness

A finite type quasi-separated morphism of algebraic spaces is proper if and
only if it satisfies the valuative criterion, if and only if every solid
valuative square admits a unique dotted lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.44.1 (Valuative criterion for properness): Let `S` be a scheme. Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S`. Assume `f` is of finite
type and quasi-separated. Then the following are equivalent: `f` is proper; the
valuative criterion holds as in Definition 67.41.1 (`ValuativeCriterion`); and
given any commutative solid diagram `Spec(K) ⟶ X` over `Spec(A) ⟶ Y` where `A`
is a valuation ring with field of fractions `K`, there exists a unique dotted
arrow `Spec(A) ⟶ X`, i.e., `f` satisfies the valuative criterion as in Schemes,
Definition 26.20.3. -/
@[stacks 0A40] #check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.proper_tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.FiniteType f] [AlgebraicSpace.QuasiSeparated f],
      List.TFAE [AlgebraicSpace.Proper f, AlgebraicSpace.ValuativeCriterion f,
        ∀ sq : AlgebraicSpace.ValuativeCommSq f,
          sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct])
