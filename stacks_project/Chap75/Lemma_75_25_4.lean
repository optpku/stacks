/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_21_2
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Perfect derived pushforward along proper morphisms of finite presentation

Along a proper morphism of finite presentation of algebraic spaces, derived
pushforward of a perfect complex is perfect when the morphism is flat, and
derived pushforward of a finitely presented module flat over the target is
perfect, with formation commuting with arbitrary cartesian base change in
both cases.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 75.25.4 (1): let `S` be a scheme and let `f : X ⟶ Y` be a proper morphism
of finite presentation of algebraic spaces over `S`. If `E` in `D(𝒪_X)` is perfect
and `f` is flat, then `Rf_* E` is a perfect object of `D(𝒪_Y)`. -/
@[stacks 0CTM]
theorem pushforwardDerived_isPerfect_of_proper_flat
    (f : X ⟶ Y) [Proper f] [FinitePresentation f] [Flat f]
    (E : ModuleDerived X) (hE : IsPerfect E) :
    IsPerfect ((Modules.pushforwardDerived f).obj E) := sorry

/-- Lemma 75.25.4 (2): let `S` be a scheme and let `f : X ⟶ Y` be a proper morphism
of finite presentation of algebraic spaces over `S`. If `E` in `D(𝒪_X)` is perfect
and `f` is flat, then formation of `Rf_* E` commutes with arbitrary cartesian base
change: for every cartesian square of algebraic spaces over `S`, the component of
`DerivedBaseChange.map` at `E` is an isomorphism `Lg^* Rf_* E ⟶ Rf'_* L(g')^* E`. -/
@[stacks 0CTM]
theorem pushforwardDerived_baseChange_isIso_of_proper_flat
    {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [IsIso (pullbackCompComparison f' g)] [IsIso (pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X) (hE : IsPerfect E) :
    IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
        (derivedPullbackPushforwardAdjunction f')
        (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app E) := sorry

/-- Lemma 75.25.4 (3): let `S` be a scheme and let `f : X ⟶ Y` be a proper morphism
of finite presentation of algebraic spaces over `S`. If `G` is a finitely presented
`𝒪_X`-module, flat over `Y`, then `Rf_* G` is a perfect object of `D(𝒪_Y)`. -/
@[stacks 0CTM]
theorem pushforwardDerived_single_isPerfect_of_proper
    (f : X ⟶ Y) [Proper f] [FinitePresentation f]
    (G : Modules X) (hG_fp : G.IsFinitePresentation)
    (hG_flat : ∀ x, Modules.flatOverAt G f x) :
    IsPerfect ((Modules.pushforwardDerived f).obj
      ((DerivedCategory.singleFunctor (Modules X) 0).obj G)) := sorry

/-- Lemma 75.25.4 (4): let `S` be a scheme and let `f : X ⟶ Y` be a proper morphism
of finite presentation of algebraic spaces over `S`. If `G` is a finitely presented
`𝒪_X`-module, flat over `Y`, then formation of `Rf_* G` commutes with arbitrary
cartesian base change: for every cartesian square of algebraic spaces over `S`, the
component of `DerivedBaseChange.map` at `(DerivedCategory.singleFunctor (Modules X) 0).obj G`
is an isomorphism `Lg^* Rf_* G ⟶ Rf'_* L(g')^* G`. -/
@[stacks 0CTM]
theorem pushforwardDerived_single_baseChange_isIso_of_proper
    {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [FinitePresentation f]
    [IsIso (pullbackCompComparison f' g)] [IsIso (pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (G : Modules X) (hG_fp : G.IsFinitePresentation)
    (hG_flat : ∀ x, Modules.flatOverAt G f x) :
    IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
        (derivedPullbackPushforwardAdjunction f')
        (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app
      ((DerivedCategory.singleFunctor (Modules X) 0).obj G)) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
