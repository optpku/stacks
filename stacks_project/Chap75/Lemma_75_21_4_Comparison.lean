/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap75.Lemma_75_21_2
public import stacks_project.Chap75.Lemma_75_21_3_Tensor

/-!
# Derived-to-underived complex comparison and tensor-pushforward base change

The cochain-level counit of derived module pullback compares `L(g')^* Q(G)` with the
localization of ordinary termwise pullback `(g')^* G`. That arrow is the right-hand
input to the tensor-pushforward base-change morphism
`Lg^* Rf_*(E ⊗^L Q(G)) ⟶ Rf'_*(L(g')^* E ⊗^L Q((g')^* G))`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The canonical comparison `L(g')^* Q(G) ⟶ Q((g')^* G)` from derived pullback of a
localized complex to the localization of its ordinary termwise pullback. -/
noncomputable def pullbackComplexComparison (g' : X' ⟶ X)
    (G : CochainComplex (Modules X) ℤ) :
    (ModuleDerived.pullback g').obj (DerivedCategory.Q.obj G) ⟶
      DerivedCategory.Q.obj
        (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G) :=
  (ModuleDerived.pullbackCochainCounit g').app G

/-- `pullbackComplexComparison` is the cochain-level total left-derived counit of module
pullback at `G`. -/
theorem pullbackComplexComparison_eq (g' : X' ⟶ X)
    (G : CochainComplex (Modules X) ℤ) :
    pullbackComplexComparison g' G =
      (ModuleDerived.pullbackCochainCounit g').app G :=
  sorry

/-- The canonical base-change morphism
`Lg^* Rf_*(E ⊗^L Q(G)) ⟶ Rf'_*(L(g')^* E ⊗^L Q((g')^* G))` whose target uses ordinary
termwise pullback of `G`. -/
noncomputable def tensorPushforwardBaseChangeMap
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g)
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ) :
    (ModuleDerived.pullback g).obj
        ((Modules.pushforwardDerived f).obj
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G))) ⟶
      (Modules.pushforwardDerived f').obj
        (DerivedTensor.Right.obj
          ((ModuleDerived.pullback g').obj E.obj)
          (DerivedCategory.Q.obj
            (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))) :=
  (DerivedBaseChange.map
      (derivedPullbackPushforwardAdjunction f)
      (derivedPullbackPushforwardAdjunction f')
      (cohomologyBaseChangeCartesianIso sq)).app
      (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G)) ≫
    (Modules.pushforwardDerived f').map
      ((ModuleDerived.pullback g').map
          (T_X.objIsoTensor E.obj (DerivedCategory.Q.obj G)).hom ≫
        (Functor.Monoidal.μIso (ModuleDerived.pullback g')
            E.obj (DerivedCategory.Q.obj G)).symm.hom ≫
          (𝟙 ((ModuleDerived.pullback g').obj E.obj) ⊗ₘ
            pullbackComplexComparison g' G) ≫
            (T_X'.objIsoTensor ((ModuleDerived.pullback g').obj E.obj)
              (DerivedCategory.Q.obj
                (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))).inv)

/-- `tensorPushforwardBaseChangeMap` is derived base change of `E ⊗^L Q(G)` followed by
`Rf'_*` of the monoidal pullback comparison and the ordinary-complex pullback comparison. -/
theorem tensorPushforwardBaseChangeMap_eq
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g)
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ) :
    tensorPushforwardBaseChangeMap g' f' f g sq T_X T_X' E G =
      (DerivedBaseChange.map
          (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction f')
          (cohomologyBaseChangeCartesianIso sq)).app
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G)) ≫
        (Modules.pushforwardDerived f').map
          ((ModuleDerived.pullback g').map
              (T_X.objIsoTensor E.obj (DerivedCategory.Q.obj G)).hom ≫
            (Functor.Monoidal.μIso (ModuleDerived.pullback g')
                E.obj (DerivedCategory.Q.obj G)).symm.hom ≫
              (𝟙 ((ModuleDerived.pullback g').obj E.obj) ⊗ₘ
                pullbackComplexComparison g' G) ≫
                (T_X'.objIsoTensor ((ModuleDerived.pullback g').obj E.obj)
                  (DerivedCategory.Q.obj
                    (((Modules.pullback g').mapHomologicalComplex
                      (up ℤ)).obj G))).inv) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
