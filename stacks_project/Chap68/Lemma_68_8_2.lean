/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree.DegreeLocus

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace

/- Lemma 68.8.2: a flat, locally finitely presented, separated, locally quasi-finite
morphism has a decreasing sequence of degree open subspaces starting at the whole target. -/
@[stacks 086T] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_degreeAtLeastOpen :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {W : Over S} (f : ofOver W ⟶ X)
      [Flat f] [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f],
      ∃ U : ℕ → OpenSubspace X,
        U 0 = OpenSubspace.id X ∧
        Antitone (fun d ↦ (U d).pointsSet) ∧
        ∀ (p : FieldValuedPoint X) (d : ℕ),
          ((∃ lift : ofOver p.overObj ⟶ (U d).X, lift ≫ (U d).ι = p.hom) ↔
            (fieldValuedPointPullbackSnd f p).HasDegreeAtLeast d))

/- Lemma 68.8.2 (1): the first open subspace in the nested degree sequence is the whole space. -/
@[stacks 086T] #check
  (AlgebraicGeometry.AlgebraicSpace.degreeAtLeastLocus_zero :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {W : Over S} (f : ofOver W ⟶ X)
      [Flat f] [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f],
      degreeAtLeastLocus f 0 = Set.univ)

/- Lemma 68.8.2 (2): the degree-at-least loci of `|X|` form a decreasing nested sequence. -/
@[stacks 086T] #check
  (AlgebraicGeometry.AlgebraicSpace.degreeAtLeastLocus_antitone :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {W : Over S} (f : ofOver W ⟶ X)
      [Flat f] [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f],
      Antitone (degreeAtLeastLocus f))

/- Lemma 68.8.2 (3): a field-valued point factors through an open subspace with this point-set
exactly when the represented fibre has degree at least `d`. -/
@[stacks 086T] #check
  (AlgebraicGeometry.AlgebraicSpace.factorsThrough_degreeAtLeastLocus_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {W : Over S} (f : ofOver W ⟶ X)
      [Flat f] [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f]
      (p : FieldValuedPoint X) (d : ℕ) {U : OpenSubspace X},
      U.pointsSet = degreeAtLeastLocus f d →
        ((∃ lift : ofOver p.overObj ⟶ U.X, lift ≫ U.ι = p.hom) ↔
          (fieldValuedPointPullbackSnd f p).HasDegreeAtLeast d))

end AlgebraicSpace
end AlgebraicGeometry
