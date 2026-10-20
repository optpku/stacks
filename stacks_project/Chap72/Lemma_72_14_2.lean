/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically
import StacksCheckRecall

/-!
# Lemma 72.14.2

A decent algebraic space over a field is geometrically integral if and only if it is
both geometrically reduced and geometrically irreducible.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CommRingCat

universe u

/- The reverse implication from geometric reducedness and irreducibility to geometric
integrality is available as a canonical instance. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible :
    ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [IsDecent X]
      [GeometricallyReduced X] [GeometricallyIrreducible X], GeometricallyIntegral X)

/- Lemma 72.14.2: let `k` be a field and let `X` be a decent algebraic space over `k`.
Then `X` is geometrically integral over `k` if and only if it is both geometrically
reduced and geometrically irreducible over `k`. -/
@[stacks 0DMX] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricallyIntegral.iff_geometricallyReduced_and_geometricallyIrreducible :
    ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [IsDecent X],
      GeometricallyIntegral X ↔ GeometricallyReduced X ∧ GeometricallyIrreducible X)
