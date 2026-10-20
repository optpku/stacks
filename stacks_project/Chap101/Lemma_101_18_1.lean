/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.FiniteType
import StacksCheckRecall

/-!
# Finite-type points of algebraic stacks, first characterization

A point of an algebraic stack is represented by a locally-of-finite-type
morphism from the spectrum of a field if and only if it is the image of a
closed point under a smooth morphism from a scheme.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 101.18.1: Let `X` be an algebraic stack. Let `x ∈ |X|`. The following
are equivalent: there exists a morphism `Spec(k) ⟶ X` which is locally of
finite type and represents `x`; and there exists a scheme `U`, a closed point
`u ∈ U`, and a smooth morphism `φ : U ⟶ X` such that `φ(u) = x`. -/
@[stacks 06FX] #check
  (AlgebraicGeometry.AlgebraicStack.existsLocallyOfFiniteTypeFieldValuedPoint_iff_existsSmoothClosedPoint :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (x : Points X),
      (∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x) ↔
        existsSmoothClosedPoint x)
