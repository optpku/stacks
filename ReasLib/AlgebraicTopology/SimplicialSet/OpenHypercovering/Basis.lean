/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.QuasiSeparated
public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Properties

/-!
# Basis-valued open hypercoverings

This leaf provides open hypercoverings whose opens lie in a prescribed topological basis.  Its
finite form uses Mathlib's ambient compactness and quasi-separatedness classes; a source-facing
bridge exposes the equivalent explicit compactness hypotheses without requiring local instances.
-/

@[expose] public section

open TopologicalSpace

universe u v

namespace SSet
namespace OpenHypercovering

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 25.11.3 (01H6): every topological basis supports an open hypercovering whose indexed
opens all belong to that basis. -/
@[stacks 01H6 "basis-valued open hypercovering"]
theorem exists_degreewiseOpensIn (B : Set (Opens X)) (hB : Opens.IsBasis B) :
    ∃ H : OpenHypercovering.{u, max u v} X, H.degreewiseOpensIn B := sorry

/-- A compact quasi-separated space with a basis of compact opens admits a basis-valued open
hypercovering with finite index type in every simplicial degree. -/
@[stacks 01H7 "finite basis-valued open hypercovering"]
theorem exists_degreewiseFiniteIn [CompactSpace X] [QuasiSeparatedSpace X]
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hB_compact : ∀ U : Opens X, U ∈ B → IsCompact (U : Set X)) :
    ∃ H : OpenHypercovering.{u, max u v} X,
      H.degreewiseOpensIn B ∧ H.degreewiseFinite := sorry

/-- Lemma 25.11.4 (01H7): the finite basis-valued existence theorem under the source's explicit
compactness and compact-intersection assumptions. -/
@[stacks 01H7 "finite basis-valued open hypercovering from explicit compactness"]
theorem exists_degreewiseFiniteIn_of_compact
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hX : IsCompact (Set.univ : Set X))
    (hB_compact : ∀ U : Opens X, U ∈ B → IsCompact (U : Set X))
    (h_inter : ∀ U V : Opens X,
      IsCompact (U : Set X) → IsCompact (V : Set X) →
        IsCompact ((U ⊓ V : Opens X) : Set X)) :
    ∃ H : OpenHypercovering.{u, max u v} X,
      H.degreewiseOpensIn B ∧ H.degreewiseFinite := sorry

end OpenHypercovering
end SSet
