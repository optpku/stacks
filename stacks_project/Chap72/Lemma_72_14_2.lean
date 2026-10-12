/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Lemma_72_14_3_Geometrically

/-!
# Lemma 72.14.2

A decent algebraic space over a field is geometrically integral if and only if it is
both geometrically reduced and geometrically irreducible.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))}

namespace GeometricallyIntegral

/-- A decent algebraic space over a field that is geometrically reduced and geometrically
irreducible is geometrically integral. -/
instance of_geometricallyReduced_of_geometricallyIrreducible
    [IsDecent X] [GeometricallyReduced X] [GeometricallyIrreducible X] :
    GeometricallyIntegral X :=
  sorry

/-- Lemma 72.14.2: let `k` be a field and let `X` be a decent algebraic space over `k`.
Then `X` is geometrically integral over `k` if and only if it is both geometrically
reduced and geometrically irreducible over `k`. -/
@[stacks 0DMX]
theorem iff_geometricallyReduced_and_geometricallyIrreducible [IsDecent X] :
    GeometricallyIntegral X ↔ GeometricallyReduced X ∧ GeometricallyIrreducible X :=
  sorry

end GeometricallyIntegral

end AlgebraicGeometry.AlgebraicSpace
