/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.RankLocus

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived.Cohomology

noncomputable section

universe u

/- Lemma 36.31.4 (1): the degree-`a` rank-`r` locus is locally closed. -/
@[stacks 0BDL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.rankLocus_isImmersion :
    {X : Scheme.{u}} →
      (E : RingedSpace.ModuleDerived X.toRingedSpace) → (a b : ℤ) → (r : ℕ) →
      RingedSpace.ModuleDerived.IsPerfect E → RingedSpace.HasTorAmplitudeIn E a b →
      IsImmersion (AlgebraicGeometry.Scheme.ModuleDerived.rankLocusι E a r))

/- Lemma 36.31.4 (2): degree-`a` cohomology on the rank locus has rank `r`. -/
@[stacks 0BDL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.rankLocus_cohomology_rank :
    {X : Scheme.{u}} →
      (E : RingedSpace.ModuleDerived X.toRingedSpace) → (a b : ℤ) → (r : ℕ) →
      RingedSpace.ModuleDerived.IsPerfect E → RingedSpace.HasTorAmplitudeIn E a b →
      SheafOfModules.IsFiniteLocallyFreeOfRank r
        (RingedSpace.ModuleDerived.cohomologySheaf
          ((RingedSpace.modulePullbackDerived
            (AlgebraicGeometry.Scheme.ModuleDerived.rankLocusι E a r).toShHom).obj E) a))

/- Lemma 36.31.4 (3): factorization through the rank locus is characterized after every
further base change. -/
@[stacks 0BDL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.rankLocus_factor_iff :
    {X Y : Scheme.{u}} →
      (E : RingedSpace.ModuleDerived X.toRingedSpace) → (a b : ℤ) → (r : ℕ) →
      RingedSpace.ModuleDerived.IsPerfect E → RingedSpace.HasTorAmplitudeIn E a b →
      (f : Y ⟶ X) →
      Nonempty (Over.mk f ⟶ Over.mk
        (AlgebraicGeometry.Scheme.ModuleDerived.rankLocusι E a r)) ↔
        ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y),
          SheafOfModules.IsFiniteLocallyFreeOfRank r
            (RingedSpace.ModuleDerived.cohomologySheaf
              ((RingedSpace.modulePullbackDerived (g ≫ f).toShHom).obj E) a))

/- Lemma 36.31.4 (4): the rank-locus morphism is of finite presentation. -/
@[stacks 0BDL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.rankLocus_finitePresentation :
    {X : Scheme.{u}} →
      (E : RingedSpace.ModuleDerived X.toRingedSpace) → (a b : ℤ) → (r : ℕ) →
      RingedSpace.ModuleDerived.IsPerfect E → RingedSpace.HasTorAmplitudeIn E a b →
      Scheme.Hom.FinitePresentation
        (AlgebraicGeometry.Scheme.ModuleDerived.rankLocusι E a r))

/- Lemma 36.31.4 (5): lower cohomology commutes with pullback from the rank locus. -/
@[stacks 0BDL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.rankLocus_comparison_isIso :
    {X Y : Scheme.{u}} →
      (E : RingedSpace.ModuleDerived X.toRingedSpace) → (a b : ℤ) → (r : ℕ) →
      RingedSpace.ModuleDerived.IsPerfect E →
      (hTor : RingedSpace.HasTorAmplitudeIn E a b) →
      (g : Y ⟶ AlgebraicGeometry.Scheme.ModuleDerived.rankLocus E a r) →
      IsIso
        (AlgebraicGeometry.Scheme.ModuleDerived.rankLocusComparison E a r g
          (AlgebraicGeometry.Scheme.ModuleDerived.rankLocusPullback_isGE E a b r hTor)
          (singlePullbackHomologyComparison_isIso
            g.toShHom
            (RingedSpace.ModuleDerived.cohomologySheaf
              ((RingedSpace.modulePullbackDerived
                (AlgebraicGeometry.Scheme.ModuleDerived.rankLocusι E a r).toShHom).obj E) a)
            a)))

/- Lemma 36.31.4 (6): a global degree-`a` fiber Betti bound makes the rank locus closed. -/
@[stacks 0BDL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.rankLocus_isClosedImmersion :
    {X : Scheme.{u}} →
      (E : RingedSpace.ModuleDerived X.toRingedSpace) → (a b : ℤ) → (r : ℕ) →
      RingedSpace.ModuleDerived.IsPerfect E → RingedSpace.HasTorAmplitudeIn E a b →
      (∀ x : X, AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti E a x ≤ r) →
      IsClosedImmersion (AlgebraicGeometry.Scheme.ModuleDerived.rankLocusι E a r))

/- Lemma 36.31.4 (7): under the fiber Betti bound, rank on the original pullback
characterizes factorization. -/
@[stacks 0BDL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.rankLocus_factor_iff_rank :
    {X Y : Scheme.{u}} →
      (E : RingedSpace.ModuleDerived X.toRingedSpace) → (a b : ℤ) → (r : ℕ) →
      RingedSpace.ModuleDerived.IsPerfect E → RingedSpace.HasTorAmplitudeIn E a b →
      (∀ x : X, AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti E a x ≤ r) →
      (f : Y ⟶ X) →
      Nonempty (Over.mk f ⟶ Over.mk
        (AlgebraicGeometry.Scheme.ModuleDerived.rankLocusι E a r)) ↔
        SheafOfModules.IsFiniteLocallyFreeOfRank r
          (RingedSpace.ModuleDerived.cohomologySheaf
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E) a))

/- Lemma 36.31.4 (8): in rank one, monicity of scalar action characterizes
factorization through the rank locus. -/
@[stacks 0BDL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.rankOneLocus_factor_iff_action_mono :
    {X Y : Scheme.{u}} →
      (E : RingedSpace.ModuleDerived X.toRingedSpace) → (a b : ℤ) →
      RingedSpace.ModuleDerived.IsPerfect E → RingedSpace.HasTorAmplitudeIn E a b →
      (∀ x : X, AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti E a x ≤ 1) →
      (f : Y ⟶ X) →
      Nonempty (Over.mk f ⟶ Over.mk
        (AlgebraicGeometry.Scheme.ModuleDerived.rankLocusι E a 1)) ↔
        Mono (SheafOfModules.Annihilator.action
          (RingedSpace.ModuleDerived.cohomologySheaf
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E) a)))
