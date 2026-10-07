module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/-
Lemma 39.23.3: A groupoid scheme with finite locally free source and target maps decomposes
into invariant clopen opens on which both maps have the same positive rank.
-/
@[stacks 03BI]
#check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantOpenRankDecomposition :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
        [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left],
      ∃ U : ℕ+ → Scheme.Opens G.U.left,
        iSup U = ⊤ ∧
          Pairwise (fun r q ↦ Disjoint (U r : Set G.U.left) (U q : Set G.U.left)) ∧
          ∀ r,
            IsClopen (U r : Set G.U.left) ∧
              G.toPreRelation.IsOpenInvariant (U r) ∧
              let UOver : Over S := Over.mk ((U r).ι ≫ G.U.hom)
              let inclusion : UOver ⟶ G.U := Over.homMk (U r).ι
              let restricted := G.pullback inclusion
              IsFiniteLocallyFreeOfRank restricted.s.left (r : ℕ) ∧
                IsFiniteLocallyFreeOfRank restricted.t.left (r : ℕ))
