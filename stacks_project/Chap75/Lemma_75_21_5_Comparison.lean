/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.InternalHomPushforward

/-! # Explicit-model internal-Hom pushforward base-change comparisons -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.internalHomPushforwardBaseChangeMap :
  ∀
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X')) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ),
    (ModuleDerived.pullback g).obj
        ((Modules.moduleDerivedPushforward f).obj
          ((ihomOf H_X E).obj (DerivedCategory.Q.obj G))) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((ihomOf H_X' ((ModuleDerived.pullback g').obj E)).obj
          (DerivedCategory.Q.obj
            (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.internalHomPushforwardBaseChangeMap_eq :
  ∀
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X')) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ),
    internalHomPushforwardBaseChangeMap g' f' f g sq H_X H_X' E G =
      (DerivedBaseChange.map
          (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction f')
          (cohomologyBaseChangeCartesianIso sq)).app
          ((ihomOf H_X E).obj (DerivedCategory.Q.obj G)) ≫
        (Modules.moduleDerivedPushforward f').map
          (Functor.PullbackInternalHom.comparisonOf H_X H_X'
              (ModuleDerived.pullback g')
              (fun A B ↦
                (Functor.Monoidal.μIso (ModuleDerived.pullback g') A B).symm)
              E (DerivedCategory.Q.obj G) ≫
            (ihomOf H_X' ((ModuleDerived.pullback g').obj E)).map
              ((ModuleDerived.pullbackCochainCounit g').app G)))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
