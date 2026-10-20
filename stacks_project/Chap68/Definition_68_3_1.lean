/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Definition 68.3.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`, and let `U`
be a scheme over `S`. Let `f : U ⟶ X` be a morphism over `S`. We say the fibres of `f` are
universally bounded if there exists an integer `n` such that for all fields `k` and all
morphisms `Spec(k) ⟶ X` the fibre product `Spec(k) ×_X U` is a finite scheme over `k` whose
degree over `k` is `≤ n`. -/
@[stacks 03JL] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyBoundedFibres_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ X),
      universallyBoundedFibres f ↔
        ∃ n : ℕ, ∀ p : FieldValuedPoint X,
          IsFinite (fieldValuedPointPullbackSnd f p) ∧
            fieldValuedPointPullbackDegree f p ≤ n)
