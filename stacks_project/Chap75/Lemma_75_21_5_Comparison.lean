/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
public import stacks_project.Chap75.Lemma_75_21_2
public import stacks_project.Chap75.Lemma_75_21_4_Comparison

/-!
# Internal-Hom pushforward base change

The canonical comparison
`Lg^* Rf_* RHom(E, Q(G)) ⟶ Rf'_* RHom(L(g')^* E, Q((g')^* G))` is derived base
change of `RHom(E, Q(G))` followed by `Rf'_*` of the pullback/internal-Hom
comparison and covariance along ordinary termwise pullback of `G`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The canonical base-change morphism
`Lg^* Rf_* RHom(E, Q(G)) ⟶ Rf'_* RHom(L(g')^* E, Q((g')^* G))` whose target uses
ordinary termwise pullback of `G`. -/
noncomputable def internalHomPushforwardBaseChangeMap
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X')) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) :
    (ModuleDerived.pullback g).obj
        ((Modules.pushforwardDerived f).obj
          ((ihomOf H_X E).obj (DerivedCategory.Q.obj G))) ⟶
      (Modules.pushforwardDerived f').obj
        ((ihomOf H_X' ((ModuleDerived.pullback g').obj E)).obj
          (DerivedCategory.Q.obj
            (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))) :=
  (DerivedBaseChange.map
      (derivedPullbackPushforwardAdjunction f)
      (derivedPullbackPushforwardAdjunction f')
      (cohomologyBaseChangeCartesianIso sq)).app
      ((ihomOf H_X E).obj (DerivedCategory.Q.obj G)) ≫
    (Modules.pushforwardDerived f').map
      (Functor.PullbackInternalHom.comparisonOf H_X H_X'
          (ModuleDerived.pullback g')
          (fun A B ↦ (Functor.Monoidal.μIso (ModuleDerived.pullback g') A B).symm)
          E (DerivedCategory.Q.obj G) ≫
        (ihomOf H_X' ((ModuleDerived.pullback g').obj E)).map
          (pullbackComplexComparison g' G))

/-- `internalHomPushforwardBaseChangeMap` is derived base change of `RHom(E, Q(G))`
followed by `Rf'_*` of the pullback/internal-Hom comparison and the ordinary-complex
pullback comparison. -/
theorem internalHomPushforwardBaseChangeMap_eq
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X')) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) :
    internalHomPushforwardBaseChangeMap g' f' f g sq H_X H_X' E G =
      (DerivedBaseChange.map
          (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction f')
          (cohomologyBaseChangeCartesianIso sq)).app
          ((ihomOf H_X E).obj (DerivedCategory.Q.obj G)) ≫
        (Modules.pushforwardDerived f').map
          (Functor.PullbackInternalHom.comparisonOf H_X H_X'
              (ModuleDerived.pullback g')
              (fun A B ↦
                (Functor.Monoidal.μIso (ModuleDerived.pullback g') A B).symm)
              E (DerivedCategory.Q.obj G) ≫
            (ihomOf H_X' ((ModuleDerived.pullback g').obj E)).map
              (pullbackComplexComparison g' G)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
