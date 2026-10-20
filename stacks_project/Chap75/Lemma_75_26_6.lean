module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RankLocus
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.LeftDerived

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

noncomputable section

universe u

/- Lemma 75.26.6. The finitely presented locally closed rank locus of lowest
cohomology, with its universal base-change property and conditional closed-locus
and rank-one criteria.

The pinned spaces source writes H^0 in its final clause. We use H^a throughout,
as in the explicitly cited scheme Lemma 36.31.4 (tag 0BDL), whose statement and
proof both use degree a; the proof constructs the locus from the differential
out of degree a. -/
@[stacks 0D21] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.exists_rankLocus :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [DerivedCategory.DerivedTensor.Right.Has (C := X.Modules)]
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b),
    ∃ (Z : AlgebraicSpace S) (j : Z ⟶ X),
      IsImmersion j ∧ FinitePresentation j ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank r
        (cohomologySheaf ((pullback j).obj E) a) ∧
      (∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
        Nonempty (Over.mk f ⟶ Over.mk j) ↔
          ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
            SheafOfModules.IsFiniteLocallyFreeOfRank r
              (cohomologySheaf ((pullback (g ≫ f)).obj E) a)) ∧
      (∀ {Y : AlgebraicSpace S} (g : Y ⟶ Z),
        IsIso
          (cohomologyPullbackComparison g ((pullback j).obj E) a
              (pullback_isGE_of_hasTorAmplitudeIn E a b hTor j)
              (singlePullbackHomologyComparison_isIso g
                (cohomologySheaf ((pullback j).obj E) a) a) ≫
            (DerivedCategory.homologyFunctor (Modules Y) a).map
              ((pullbackCompComparison g j).app E))) ∧
      ((∀ x : Points X, fiberBetti E a x ≤ r) →
        IsClosedImmersion j ∧
        (∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
          Nonempty (Over.mk f ⟶ Over.mk j) ↔
            SheafOfModules.IsFiniteLocallyFreeOfRank r
              (cohomologySheaf ((pullback f).obj E) a)) ∧
        (r = 1 → ∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
          Nonempty (Over.mk f ⟶ Over.mk j) ↔
            Mono (SheafOfModules.RingedSite.Annihilator.action
              (Modules.liftModule (cohomologySheaf ((pullback f).obj E) a))))))
