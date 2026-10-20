/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints.Etale
import StacksCheckRecall

/-!
# Finite-type points of algebraic spaces, first characterization

A point of an algebraic space is represented by a locally-of-finite-type
morphism from the spectrum of a field if and only if it is the image of a
closed point under an étale morphism from a scheme.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.25.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x : Points X`. The following are equivalent: there exists a morphism
`Spec(k) ⟶ X` which is locally of finite type and represents `x`; and there
exists a scheme `U`, a closed point `u ∈ U`, and an étale morphism
`φ : U ⟶ X` such that `φ(u) = x`. -/
@[stacks 06EF] #check
  (AlgebraicGeometry.AlgebraicSpace.isFiniteTypePoint_iff_existsEtaleClosedPoint :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : AlgebraicSpace.Points X),
      (∃ p : AlgebraicSpace.FieldValuedPoint X,
        AlgebraicSpace.LocallyOfFiniteType p.hom ∧ AlgebraicSpace.Points.mk p = x) ↔
      ∃ (U : Over S) (u : U.left) (φ : AlgebraicSpace.ofOver U ⟶ X),
        u ∈ closedPoints U.left ∧ AlgebraicSpace.Etale φ ∧
          AlgebraicSpace.Points.mapOfOver φ u = x)
