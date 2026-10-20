module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.TargetLocus
import StacksCheckRecall

/-!
# Invariance of the target locus of a groupoid source map
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 79.6.1: Let `B → S` be as in Section 79.2. Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `B`. Let `τ ∈ {fppf, étale, smooth, syntomic}`.
Let `P` be a property of morphisms of algebraic spaces which is `τ`-local on the
target. Assume `{s : R ⟶ U}` and `{t : R ⟶ U}` are coverings for the `τ`-topology.
Let `W ⊂ U` be the maximal open subspace such that `s⁻¹(W) ⟶ W` has property `P`,
namely `W = AlgebraicSpace.targetLocus P G.s.left`. Then `W` is `R`-invariant
in the sense that `t(s⁻¹(W)) ⊂ W`. -/
@[stacks 044Z]
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isOpenInvariant_targetLocus_source :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K],
    AlgebraicSpace.isFppfToEtalePrecoverage K →
    Presieve.singleton G.s.left ∈ K.coverings G.U.left →
    Presieve.singleton G.t.left ∈ K.coverings G.U.left →
    CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left
      (AlgebraicSpace.targetLocus P G.s.left).ι)
