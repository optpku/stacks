/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Subring

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.46.5: let `A ⊆ B` be a ring extension such that `Spec(B) → Spec(A)` is a
universal homeomorphism inducing isomorphisms on residue fields. If `A ≠ B`, then there is
some `b ∈ B` with `b ∉ A`, `b ^ 2 ∈ A`, and `b ^ 3 ∈ A`. -/
@[stacks 0CNB] #check
  (AlgebraicGeometry.UniversalHomeomorphism.exists_not_mem_sq_cube_mem_of_residueFieldMap_isIso :
    ∀ {B : Type u} [CommRing B] (A : Subring B),
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom A.subtype)) →
        (∀ x : Spec (CommRingCat.of B),
          IsIso ((Spec.map (CommRingCat.ofHom A.subtype)).residueFieldMap x)) →
          A ≠ ⊤ → ∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A)
