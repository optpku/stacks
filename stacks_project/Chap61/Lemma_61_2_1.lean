/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Spectral.Split
import StacksCheckRecall

/-!
# Lemma 61.2.1

A spectral space has finite pairwise disjoint clopen refinements of every
open cover if and only if the canonical map from closed points to connected
components is bijective. Unique closed-point specialization with a closed
set of closed points is a sufficient condition.
-/

@[expose] public section

open Set Topology

universe u

/- Lemma 61.2.1 (1): for a spectral space `X`, every open cover of `X` admits a
finite pairwise disjoint clopen decomposition refinement if and only if
`ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X`
is bijective. -/
@[stacks 0968] #check
  (SpectralSpace.hasFiniteDisjointClopenCoverRefinement_iff_bijective_fromClosedPoints :
    ∀ {X : Type u} [TopologicalSpace X] [SpectralSpace X],
      HasFiniteDisjointClopenCoverRefinement X ↔
        Function.Bijective
          (ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X))

/- Lemma 61.2.1 (2): if `X` is spectral, `closedPoints X` is closed, and every
point of `X` specializes to a unique closed point, then
`ConnectedComponents.fromClosedPoints` is bijective. -/
@[stacks 0968] #check
  (SpectralSpace.bijective_fromClosedPoints_of_uniqueClosedPointSpecialization :
    ∀ {X : Type u} [TopologicalSpace X] [SpectralSpace X],
      IsClosed (closedPoints X) → HasUniqueClosedPointSpecialization X →
        Function.Bijective
          (ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X))
