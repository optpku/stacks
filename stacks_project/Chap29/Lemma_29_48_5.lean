/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

/-!
# Lemma 29.48.5

The reusable constant-rank decomposition API is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations`.
-/

/- Lemma 29.48.5: finite locally free morphisms have a clopen base decomposition on which the
rank is constant. -/
@[stacks 04MH] #check
  (AlgebraicGeometry.exists_clopen_degree_decomposition_of_isFiniteLocallyFree :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsFiniteLocallyFree f],
      ∃ Sdegree : ℕ → S.Opens,
        iSup Sdegree = ⊤ ∧
          Pairwise (fun d e ↦ Disjoint (Sdegree d : Set S) (Sdegree e : Set S)) ∧
          (∀ d, IsClopen (Sdegree d : Set S)) ∧
          ∀ d, IsFiniteLocallyFreeOfRank (f ∣_ (Sdegree d)) d)
