/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_10_3_TargetLocus
public import stacks_project.Chap78.Definition_78_18_1_Invariant
public import stacks_project.Chap78.Lemma_78_29_1_Diagram

/-!
# Invariance of the target locus of a groupoid stabilizer map
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 79.6.2: Let `B → S` be as in Section 79.2. Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `B`. Let `G ⟶ U` be its stabilizer group
algebraic space. Let `τ ∈ {fppf, étale, smooth, syntomic}`. Let `P` be a
property of morphisms of algebraic spaces which is `τ`-local on the target.
Assume `{s : R ⟶ U}` and `{t : R ⟶ U}` are coverings for the `τ`-topology.
Let `W ⊂ U` be the maximal open subspace such that `G_W ⟶ W` has property `P`,
namely `W = AlgebraicSpace.targetLocus P G.stabilizerMap.left`. Then `W` is
`R`-invariant in the sense of `G.toPreRelation.IsOpenInvariant`. -/
@[stacks 06R4]
theorem isOpenInvariant_targetLocus_stabilizerMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : AlgebraicSpace.isFppfToEtalePrecoverage K)
    (hs : Presieve.singleton G.s.left ∈ K.coverings G.U.left)
    (ht : Presieve.singleton G.t.left ∈ K.coverings G.U.left) :
    G.toPreRelation.IsOpenInvariant
      (AlgebraicSpace.targetLocus P G.stabilizerMap.left) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
