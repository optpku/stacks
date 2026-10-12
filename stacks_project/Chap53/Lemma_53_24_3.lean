/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge.Decomposition

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.SchemeOverField

universe u

/- Lemma 53.24.3: for a proper one-dimensional scheme with constant global functions and
at-worst-nodal singularities, every rational bridge becomes a finite disjoint union of rational
bridges after base change along any field extension. -/
@[stacks 0E65] #check (AlgebraicGeometry.RationalBridge.baseChange_decomposition :
  ∀ {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (B : RationalBridge X),
    Nonempty (RationalBridge.BaseChangeDecomposition K X B))
