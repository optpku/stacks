module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorAmplitude
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FiberEulerCharacteristic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Single
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Annihilator

/-! # Rank loci of lowest cohomology of perfect derived modules

The finite locally free rank of lowest derived cohomology is universally represented
by a finitely presented locally closed subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- A perfect derived module of Tor-amplitude `[a, b]` has a finitely presented locally
closed rank-`r` locus for its degree-`a` cohomology, characterized after every further
base change. Lowest cohomology commutes with pullback from this locus. If every degree-`a`
fiber Betti number is at most `r`, the locus is closed and a single pullback tests
factorization; when `r = 1`, monicity of scalar action also tests factorization. -/
theorem exists_rankLocus {S : Scheme.{u}} {X : AlgebraicSpace S}
    [DerivedCategory.DerivedTensor.Right.Has (C := X.Modules)]
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b) :
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
              (Modules.liftModule (cohomologySheaf ((pullback f).obj E) a))))) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
