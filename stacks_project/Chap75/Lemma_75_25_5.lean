module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_21_2

/-!
# Derived pushforward of pseudo-coherent complexes

Along a flat, proper morphism of finite presentation of algebraic spaces, derived
pushforward sends pseudo-coherent objects of `D(𝒪_X)` to pseudo-coherent objects of
`D(𝒪_Y)`, and formation of that pushforward commutes with arbitrary cartesian base
change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 75.25.5 (1): let `S` be a scheme and let `f : X ⟶ Y` be a flat, proper
morphism of finite presentation of algebraic spaces over `S`. If `E` in `D(𝒪_X)` is
pseudo-coherent, then `(Modules.pushforwardDerived f).obj E` is a pseudo-coherent
object of `D(𝒪_Y)`. -/
@[stacks 0CTN]
theorem pushforwardDerived_isPseudoCoherent_of_isPseudoCoherent
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (E : ModuleDerived X) (hE : IsPseudoCoherent X E) :
    IsPseudoCoherent Y ((Modules.pushforwardDerived f).obj E) := sorry

/-- Lemma 75.25.5 (2): let `S` be a scheme and let `f : X ⟶ Y` be a flat, proper
morphism of finite presentation of algebraic spaces over `S`. If `E` in `D(𝒪_X)` is
pseudo-coherent, then for every cartesian square of algebraic spaces over `S` the
component of `DerivedBaseChange.map` at `E` is an isomorphism. -/
@[stacks 0CTN]
theorem pushforwardDerived_baseChange_isIso_of_isPseudoCoherent
    {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [IsIso (pullbackCompComparison f' g)] [IsIso (pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X) (hE : IsPseudoCoherent X E) :
    IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
        (derivedPullbackPushforwardAdjunction f')
        (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
