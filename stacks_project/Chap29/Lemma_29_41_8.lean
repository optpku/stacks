/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import StacksCheckRecall

/-!
# Lemma 29.41.8

A universally closed morphism is quasi-compact.

@stack 04XU
-/

@[expose] public section

universe u

open CategoryTheory

/- Lemma 29.41.8: A universally closed morphism of schemes is quasi-compact. -/
@[stacks 04XU] #check
  (AlgebraicGeometry.instQuasiCompactOfUniversallyClosed :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.UniversallyClosed f], AlgebraicGeometry.QuasiCompact f)
