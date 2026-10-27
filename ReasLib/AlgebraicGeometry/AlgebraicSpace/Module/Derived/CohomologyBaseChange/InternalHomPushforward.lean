/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison

/-! # Internal-Hom pushforward base change for relatively flat complexes -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The canonical internal-Hom pushforward base-change morphism uses derived pullback
of the first Hom argument and ordinary termwise pullback of the coefficient complex. -/
noncomputable def internalHomPushforwardBaseChange
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) :
    (ModuleDerived.pullback g).obj
        ((Modules.moduleDerivedPushforward f).obj
          ((ModuleDerived.InternalHom.functor E).obj (DerivedCategory.Q.obj G))) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj E)).obj
          (DerivedCategory.Q.obj
            (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))) :=
  (DerivedBaseChange.map
      (derivedPullbackPushforwardAdjunction f)
      (derivedPullbackPushforwardAdjunction f')
      (cohomologyBaseChangeCartesianIso sq)).app
      ((ModuleDerived.InternalHom.functor E).obj (DerivedCategory.Q.obj G)) ≫
    (Modules.moduleDerivedPushforward f').map
      (ModuleDerived.InternalHom.canonicalPullbackComparison g' E (DerivedCategory.Q.obj G) ≫
        (ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj E)).map
          ((ModuleDerived.pullbackCochainCounit g').app G))

/-- The canonical internal-Hom pushforward comparison is the base-change mate followed
by pushforward of the canonical pullback–Hom comparison and the ordinary-pullback counit. -/
theorem internalHomPushforwardBaseChange_eq
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) :
    internalHomPushforwardBaseChange g' f' f g sq E G =
      (DerivedBaseChange.map
          (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction f')
          (cohomologyBaseChangeCartesianIso sq)).app
          ((ModuleDerived.InternalHom.functor E).obj (DerivedCategory.Q.obj G)) ≫
        (Modules.moduleDerivedPushforward f').map
          (ModuleDerived.InternalHom.canonicalPullbackComparison g' E (DerivedCategory.Q.obj G) ≫
            (ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj E)).map
              ((ModuleDerived.pullbackCochainCounit g').app G)) := rfl

/-- For a quasi-compact and quasi-separated morphism of algebraic spaces, derived
pushforward of canonical derived sheaf Hom from a perfect derived module and a bounded-above
degreewise quasi-coherent complex flat over the target commutes with arbitrary base change.
The coefficient complex on the right is pulled back termwise. -/
theorem pushforwardInternalHomBaseChange_isIso_of_isPerfect
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (hE : ModuleDerived.IsPerfect E)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x) :
    IsIso (internalHomPushforwardBaseChange g' f' f g sq E G) :=
  sorry

/-- For a quasi-compact and quasi-separated morphism of algebraic spaces, derived
pushforward of canonical derived sheaf Hom from a pseudo-coherent derived module and a bounded
degreewise quasi-coherent complex flat over the target commutes with arbitrary base change.
The coefficient complex on the right is pulled back termwise. -/
theorem pushforwardInternalHomBaseChange_isIso_of_isPseudoCoherent
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (hE : IsPseudoCoherent X E)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x) :
    IsIso (internalHomPushforwardBaseChange g' f' f g sq E G) :=
  sorry

/-- The canonical internal-Hom pushforward comparison is invertible when perfectness,
boundedness, degreewise quasi-coherence and relative flatness are available as proof instances. -/
instance internalHomPushforwardBaseChange_isIso_of_isPerfect
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ)
    [Fact (ModuleDerived.IsPerfect E)]
    [Fact (CochainComplex.minus (Modules X) G)]
    [∀ n : ℤ, (G.X n).IsQuasicoherent]
    [Fact (∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x)] :
    IsIso (internalHomPushforwardBaseChange g' f' f g sq E G) :=
  pushforwardInternalHomBaseChange_isIso_of_isPerfect g' f' f g sq E G
    (Fact.out : ModuleDerived.IsPerfect E)
    (Fact.out : CochainComplex.minus (Modules X) G)
    (fun n ↦ inferInstanceAs (G.X n).IsQuasicoherent)
    (Fact.out : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x)

/-- The canonical internal-Hom pushforward comparison is invertible when pseudo-coherence,
boundedness, degreewise quasi-coherence and relative flatness are available as proof instances. -/
instance internalHomPushforwardBaseChange_isIso_of_isPseudoCoherent
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ)
    [Fact (IsPseudoCoherent X E)]
    [Fact (CochainComplex.bounded (Modules X) G)]
    [∀ n : ℤ, (G.X n).IsQuasicoherent]
    [Fact (∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x)] :
    IsIso (internalHomPushforwardBaseChange g' f' f g sq E G) :=
  pushforwardInternalHomBaseChange_isIso_of_isPseudoCoherent g' f' f g sq E G
    (Fact.out : IsPseudoCoherent X E)
    (Fact.out : CochainComplex.bounded (Modules X) G)
    (fun n ↦ inferInstanceAs (G.X n).IsQuasicoherent)
    (Fact.out : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x)

/-- A base-change morphism for internal Hom presented using explicit ambient monoidal and
closed structures. Its target uses ordinary termwise pullback of the coefficient complex. -/
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
        ((Modules.moduleDerivedPushforward f).obj
          ((ihomOf H_X E).obj (DerivedCategory.Q.obj G))) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((ihomOf H_X' ((ModuleDerived.pullback g').obj E)).obj
          (DerivedCategory.Q.obj
            (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))) :=
  (DerivedBaseChange.map
      (derivedPullbackPushforwardAdjunction f)
      (derivedPullbackPushforwardAdjunction f')
      (cohomologyBaseChangeCartesianIso sq)).app
      ((ihomOf H_X E).obj (DerivedCategory.Q.obj G)) ≫
    (Modules.moduleDerivedPushforward f').map
      (Functor.PullbackInternalHom.comparisonOf H_X H_X'
          (ModuleDerived.pullback g')
          (fun A B ↦ (Functor.Monoidal.μIso (ModuleDerived.pullback g') A B).symm)
          E (DerivedCategory.Q.obj G) ≫
        (ihomOf H_X' ((ModuleDerived.pullback g').obj E)).map
          ((ModuleDerived.pullbackCochainCounit g').app G))

/-- The explicit-model internal-Hom pushforward comparison is the base-change mate followed
by pushforward of the chosen closed-structure comparison and ordinary-pullback counit. -/
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
        (Modules.moduleDerivedPushforward f').map
          (Functor.PullbackInternalHom.comparisonOf H_X H_X'
              (ModuleDerived.pullback g')
              (fun A B ↦
                (Functor.Monoidal.μIso (ModuleDerived.pullback g') A B).symm)
              E (DerivedCategory.Q.obj G) ≫
            (ihomOf H_X' ((ModuleDerived.pullback g').obj E)).map
              ((ModuleDerived.pullbackCochainCounit g').app G)) :=
  rfl


end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
