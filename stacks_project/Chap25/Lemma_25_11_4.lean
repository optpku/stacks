/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Basis
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u

/- Lemma 25.11.4 (01H7): under the source's explicit quasi-compactness hypotheses there is a
basis-valued open hypercovering whose index type is finite in every simplicial degree. -/
@[stacks 01H7 "Lemma 25.11.4"]
#check (@SSet.OpenHypercovering.exists_degreewiseFiniteIn_of_compact :
  ∀ {X : Type u} [TopologicalSpace X]
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hX : IsCompact (Set.univ : Set X))
    (hB_compact : ∀ U : Opens X, U ∈ B → IsCompact (U : Set X))
    (h_inter : ∀ U V : Opens X,
      IsCompact (U : Set X) → IsCompact (V : Set X) →
        IsCompact ((U ⊓ V : Opens X) : Set X)),
      ∃ H : SSet.OpenHypercovering.{u, u} X,
        H.degreewiseOpensIn B ∧ H.degreewiseFinite)

/- The reusable owner packages the canonical ambient assumptions as Mathlib typeclasses. -/
#check @SSet.OpenHypercovering.exists_degreewiseFiniteIn

/- Degree `0` is the initial finite cover; every successor cover has a finite matching-index
fiber, including the pairwise cover in degree `1`. -/
#check @SSet.OpenHypercovering.degreewiseFinite.zero

@[stacks 01H7 "finite matching coverings"]
#check @SSet.OpenHypercovering.degreewiseFinite.matchingIndices
