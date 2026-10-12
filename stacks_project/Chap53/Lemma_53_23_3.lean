/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail.BaseChange

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

/- Lemma 53.23.3: for a proper one-dimensional scheme with constant global functions and
at-worst-nodal singularities, every rational tail becomes a finite disjoint union of rational
tails after base change along any field extension. -/
@[stacks 0E3I] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.baseChange_decomposition :
    ∀ {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
      (X : AlgebraicGeometry.SchemeOverField k) [Algebraic X] [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_nodal : AlgebraicGeometry.SchemeOverField.atWorstNodal X)
      (C : AlgebraicGeometry.SchemeOverField.RationalTail X),
      Nonempty
        (AlgebraicGeometry.SchemeOverField.RationalTail.BaseChangeDecomposition K X C))
