module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap76.Lemma_76_52_4_Relative

/-!
# Dual of a relatively perfect internal Hom after derived pushforward

Along a proper, flat, finitely presented morphism of algebraic spaces with
quasi-compact quasi-separated target, the derived pushforward of the internal
Hom from a pseudo-coherent complex to a relatively perfect complex is the
internal Hom of a pseudo-coherent complex into the structure sheaf, and the
same complex remains valid after every cartesian base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 76.52.11: let `S` be a scheme and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `Y` is quasi-compact and quasi-separated, `f`
is proper, flat, and of finite presentation, `E` in `D(𝒪_X)` is `Y`-perfect, and
`K` in `D(𝒪_X)` is pseudo-coherent. Then there exists a pseudo-coherent `L` in
`D(𝒪_Y)` such that `(Modules.pushforwardDerived f).obj ((ihom K).obj E)` is
isomorphic to `(ihom L).obj (𝟙_ (ModuleDerived Y))`, and the same identification
holds after every cartesian base change. -/
@[stacks 0DKY]
theorem exists_pseudoCoherent_dual (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [Proper f] [Flat f] [FinitePresentation f]
    [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived Y)] [MonoidalClosed (ModuleDerived Y)]
    (E K : ModuleDerived X) (hE : IsPerfectRelativeTo f E)
    (hK : IsPseudoCoherent X K) :
    ∃ L : ModuleDerived Y,
      IsPseudoCoherent Y L ∧
        IsIsomorphic ((Modules.pushforwardDerived f).obj ((ihom K).obj E))
          ((ihom L).obj (𝟙_ (ModuleDerived Y))) ∧
        ∀ {X' Y' : AlgebraicSpace S}
          [MonoidalCategory (ModuleDerived X')] [MonoidalClosed (ModuleDerived X')]
          [MonoidalCategory (ModuleDerived Y')] [MonoidalClosed (ModuleDerived Y')]
          (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
          IsPullback g' f' f g →
            IsIsomorphic
              ((Modules.pushforwardDerived f').obj
                ((ihom ((ModuleDerived.pullback g').obj K)).obj
                  ((ModuleDerived.pullback g').obj E)))
              ((ihom ((ModuleDerived.pullback g).obj L)).obj
                (𝟙_ (ModuleDerived Y'))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
