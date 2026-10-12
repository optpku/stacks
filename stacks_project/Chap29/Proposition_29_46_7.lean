/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Subring.SquareCube

open AlgebraicGeometry CategoryTheory

universe u

/- Proposition 29.46.7: for a ring extension `A ⊆ B`, the affine spectrum map
`Spec(B) ⟶ Spec(A)` is a universal homeomorphism inducing isomorphisms on residue fields if and
only if every finite subset of `B` lies in a finite sequence of adjunctions whose new generators
have square and cube in the subring generated at the preceding stage. -/
@[stacks 0CND] #check
  (AlgebraicGeometry.UniversalHomeomorphism.SquareCube.specMap_subtype_iff :
    ∀ {B : Type u} [CommRing B] (A : Subring B),
      (UniversalHomeomorphism (Spec.map (CommRingCat.ofHom A.subtype)) ∧
        ∀ x : Spec (CommRingCat.of B),
          IsIso ((Spec.map (CommRingCat.ofHom A.subtype)).residueFieldMap x)) ↔
        A.IsFilteredBySquareCubeAdjunctions)
