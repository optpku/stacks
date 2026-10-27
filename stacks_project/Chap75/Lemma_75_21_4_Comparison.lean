/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.TensorPushforward

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
noncomputable abbrev pullbackComplexComparison (g' : X' ⟶ X)
    (G : CochainComplex (Modules X) ℤ) :
    (ModuleDerived.pullback g').obj (DerivedCategory.Q.obj G) ⟶
      DerivedCategory.Q.obj
        (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G) :=
  (ModuleDerived.pullbackCochainCounit g').app G


#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.tensorPushforwardBaseChangeMap :
  ∀
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g)
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ),
    (ModuleDerived.pullback g).obj
        ((Modules.moduleDerivedPushforward f).obj
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G))) ⟶
      (Modules.moduleDerivedPushforward f').obj
        (DerivedTensor.Right.obj
          ((ModuleDerived.pullback g').obj E.obj)
          (DerivedCategory.Q.obj
            (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.tensorPushforwardBaseChangeMap_eq :
  ∀
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g)
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ),
    tensorPushforwardBaseChangeMap g' f' f g sq T_X T_X' E G =
      (DerivedBaseChange.map
          (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction f')
          (cohomologyBaseChangeCartesianIso sq)).app
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G)) ≫
        (Modules.moduleDerivedPushforward f').map
          ((ModuleDerived.pullback g').map
              (T_X.objIsoTensor E.obj (DerivedCategory.Q.obj G)).hom ≫
            (Functor.Monoidal.μIso (ModuleDerived.pullback g')
                E.obj (DerivedCategory.Q.obj G)).symm.hom ≫
              (𝟙 ((ModuleDerived.pullback g').obj E.obj) ⊗ₘ
                (ModuleDerived.pullbackCochainCounit g').app G) ≫
                (T_X'.objIsoTensor ((ModuleDerived.pullback g').obj E.obj)
                  (DerivedCategory.Q.obj
                    (((Modules.pullback g').mapHomologicalComplex
                      (up ℤ)).obj G))).inv))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
