/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import stacks_project.Chap75.Lemma_75_26_6_Pullback
import stacks_project.Chap75.Lemma_75_26_6_RankLocus

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

/- Lemma 75.26.6 (1): the degree-`a` rank-`r` locus is locally closed. -/
@[stacks 0D21] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocus_isImmersion :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      (E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived X) → (a b : ℤ) → (r : ℕ) →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect E →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeIn E a b →
      IsImmersion (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocusι E a r))

/- Lemma 75.26.6 (2): degree-`a` cohomology on the rank locus has rank `r`. -/
@[stacks 0D21] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocus_cohomology_rank :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      (E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived X) → (a b : ℤ) → (r : ℕ) →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect E →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeIn E a b →
      SheafOfModules.IsFiniteLocallyFreeOfRank r
        (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologySheaf
          ((AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullback
            (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocusι E a r)).obj E) a))

/- Lemma 75.26.6 (3): factorization through the rank locus is characterized after every
further base change. -/
@[stacks 0D21] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocus_factor_iff :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
      (E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived X) → (a b : ℤ) → (r : ℕ) →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect E →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeIn E a b →
      (f : Y ⟶ X) →
      Nonempty (Over.mk f ⟶ Over.mk
        (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocusι E a r)) ↔
        ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
          SheafOfModules.IsFiniteLocallyFreeOfRank r
            (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologySheaf
              ((AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullback (g ≫ f)).obj E) a))

/- Lemma 75.26.6 (4): the rank-locus morphism is of finite presentation. -/
@[stacks 0D21] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocus_finitePresentation :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      (E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived X) → (a b : ℤ) → (r : ℕ) →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect E →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeIn E a b →
      FinitePresentation
        (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocusι E a r))

/- Lemma 75.26.6 (5): lower cohomology commutes with pullback from the rank locus. -/
@[stacks 0D21] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocus_comparison_isIso :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
      (E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived X) → (a b : ℤ) → (r : ℕ) →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect E →
      (hTor : AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeIn E a b) →
      (g : Y ⟶ AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocus E a r) →
      IsIso
        (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocusComparison E a r g
          (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocusPullback_isGE E a b r hTor)
          (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.singlePullbackHomologyComparison_isIso g
            (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologySheaf
              ((AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullback
                (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocusι E a r)).obj E) a)
            a)))

/- Lemma 75.26.6 (6): a global degree-`a` fiber Betti bound makes the rank locus closed. -/
@[stacks 0D21] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocus_isClosedImmersion :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      (E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived X) → (a b : ℤ) → (r : ℕ) →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect E →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeIn E a b →
      (∀ x : Points X, AlgebraicGeometry.AlgebraicSpace.ModuleDerived.fiberBetti E a x ≤ r) →
      IsClosedImmersion
        (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocusι E a r))

/- Lemma 75.26.6 (7): under the fiber Betti bound, rank on the original pullback
characterizes factorization. -/
@[stacks 0D21] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocus_factor_iff_rank :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
      (E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived X) → (a b : ℤ) → (r : ℕ) →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect E →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeIn E a b →
      (∀ x : Points X, AlgebraicGeometry.AlgebraicSpace.ModuleDerived.fiberBetti E a x ≤ r) →
      (f : Y ⟶ X) →
      Nonempty (Over.mk f ⟶ Over.mk
        (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocusι E a r)) ↔
        SheafOfModules.IsFiniteLocallyFreeOfRank r
          (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologySheaf
            ((AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullback f).obj E) a))

/- Lemma 75.26.6 (8): in rank one, monicity of scalar action characterizes
factorization through the rank locus. -/
@[stacks 0D21] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankOneLocus_factor_iff_action_mono :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
      (E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived X) → (a b : ℤ) →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect E →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeIn E a b →
      (∀ x : Points X, AlgebraicGeometry.AlgebraicSpace.ModuleDerived.fiberBetti E a x ≤ 1) →
      (f : Y ⟶ X) →
      Nonempty (Over.mk f ⟶ Over.mk
        (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.rankLocusι E a 1)) ↔
        Mono
          (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.endomorphismAction
            (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologySheaf
              ((AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullback f).obj E) a)))
