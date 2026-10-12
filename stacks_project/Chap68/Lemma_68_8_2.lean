/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap68.Lemma_68_8_2_DegreeLocus

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace

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
