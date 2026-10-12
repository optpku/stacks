/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Automorphism.Rigidity
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.32.1 (1): a topologically trivial automorphism of a reduced finite-type scheme over a
field pulls every coherent module back to an isomorphic module. -/
@[stacks 0G05] #check
  (AlgebraicGeometry.SchemeOverField.Automorphism.pullback_isIsomorphic_of_isCoherent_of_eqOnPoints :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsReduced X.left]
      [AlgebraicGeometry.Scheme.Hom.FiniteType X.hom]
      (f : X ≅ X),
      (∀ x : X.left, f.hom.left x = x) →
      ∀ (ℱ : X.left.Modules) [ℱ.IsCoherent],
        CategoryTheory.IsIsomorphic
          ((AlgebraicGeometry.Scheme.Modules.pullback f.hom.left).obj ℱ) ℱ)

/- Lemma 33.32.1 (2): if every irreducible component also has positive dimension, the
automorphism is the identity. -/
@[stacks 0G05] #check
  (AlgebraicGeometry.SchemeOverField.Automorphism.hom_eq_id_of_eqOnPoints_of_irreducibleComponents_posDim :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsReduced X.left]
      [AlgebraicGeometry.Scheme.Hom.FiniteType X.hom]
      (f : X ≅ X),
      (∀ x : X.left, f.hom.left x = x) →
      (∀ Z : irreducibleComponents X.left, 0 < topologicalKrullDim Z) →
      f.hom = 𝟙 X)
