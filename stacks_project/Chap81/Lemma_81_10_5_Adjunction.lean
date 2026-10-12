/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

/-!
# Derived pullback-pushforward adjunction on algebraic spaces

The unbounded derived adjunction `Lf^* ⊣ Rf_*` on `D(𝒪)` associated to a
morphism of algebraic spaces, obtained from the underived module adjunction by
`Adjunction.TotalDerived.HasPair.derived`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Homotopy-to-derived module pullback admits a total left derived functor. -/
instance modulePullbackToDerived_hasLeftDerived {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    ((Modules.pullback f).mapHomotopyCategory (up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory (Modules Y) (up ℤ) ⥤
          ModuleDerived Y)).HasLeftDerivedFunctor (ModuleQis X) :=
  (instModulePullbackToDerivedHasLeftDerivedFunctor f :
    (modulePullbackToDerived f).HasLeftDerivedFunctor (ModuleQis X))

/-- Homotopy-to-derived module pushforward admits a total right derived functor. -/
instance modulePushforwardToDerived_hasRightDerived {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    ((Modules.pushforward f).mapHomotopyCategory (up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤
          ModuleDerived X)).HasRightDerivedFunctor (ModuleQis Y) :=
  Functor.RightDerived.KInjective.hasDerived (Modules.pushforward f)

/-- Homotopy-level pullback and pushforward form an absolute derived adjunction pair. -/
instance modulePullbackPushforwardHasPair {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    Adjunction.TotalDerived.HasPair
      (G := (Modules.pullback f).mapHomotopyCategory (up ℤ))
      (F := (Modules.pushforward f).mapHomotopyCategory (up ℤ))
      (ModuleQis X) (ModuleQis Y)
      (L1 := DerivedCategory.Qh) (L2 := DerivedCategory.Qh) :=
  sorry

/-- The unbounded derived adjunction `Lf^* ⊣ Rf_*` on `D(𝒪)`. -/
noncomputable def modulePullbackDerivedPushforwardAdjunction {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    modulePullbackDerived f ⊣ Modules.pushforwardDerived f :=
  Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction (Modules.pullbackPushforwardAdjunction f))
    (ModuleQis X) (ModuleQis Y)

/-- The derived adjunction `Lf^* ⊣ Rf_*` is the total-derived adjunction of
homotopy-level module pullback and pushforward. -/
theorem modulePullbackDerivedPushforwardAdjunction_eq {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    modulePullbackDerivedPushforwardAdjunction f =
      Adjunction.TotalDerived.HasPair.derived
        (Adjunction.mapHomotopyCategoryAdjunction (Modules.pullbackPushforwardAdjunction f))
        (ModuleQis X) (ModuleQis Y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
