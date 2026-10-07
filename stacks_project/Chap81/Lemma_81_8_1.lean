module

public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap81.Lemma_81_6_2_Pushout
public import stacks_project.Chap81.Lemma_81_8_1_Comparison

/-!
# Lemma 81.8.1

In a pushout of algebraic spaces along a thickening and an affine morphism, every
pseudo-coherent triple in the derived-module fibre product lies in the essential
image of derived pullback from `Y'`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.8.1: Let `S` be a scheme. Consider a pushout square of algebraic spaces
over `S` as in Lemma 81.6.2, and assume `i` is a thickening. Then the essential image
of the derived-pullback functor `D(𝒪_{Y'}) ⥤ D(𝒪_Y) ×_{D(𝒪_X)} D(𝒪_{X'})` contains
every triple `(M, K', α)` where `M : ModuleDerived Y` and `K' : ModuleDerived X'` are
pseudo-coherent and `α : Lf^* M ≅ Li^* K'`. -/
@[stacks 0DL7]
theorem modulePullbackDerived.pushoutSquareFunctor_essImage_of_pseudoCoherent
    {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    [IsThickening i] [Affine f]
    [IsIso (modulePullbackDerived.compComparison f j)]
    [IsIso (modulePullbackDerived.compComparison i f')]
    (h : IsPushout i f f' j) (M : ModuleDerived Y) (K' : ModuleDerived X')
    (hM : IsPseudoCoherent Y M) (hK' : IsPseudoCoherent X' K')
    (α : (modulePullbackDerived f).obj M ≅ (modulePullbackDerived i).obj K') :
    (modulePullbackDerived.pushoutSquareFunctor h.toCommSq).essImage
      (modulePullbackDerived.pullbackTriple M K' α) := sorry

/-- A triple in `modulePullbackDerived f ⊡ modulePullbackDerived i` with
pseudo-coherent components lies in the essential image of
`modulePullbackDerived.pushoutSquareFunctor` along a Lemma 81.6.2 pushout. -/
theorem modulePullbackDerived.pushoutSquareFunctor_essImage_of_pseudoCoherent_obj
    {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    [IsThickening i] [Affine f]
    [IsIso (modulePullbackDerived.compComparison f j)]
    [IsIso (modulePullbackDerived.compComparison i f')]
    (h : IsPushout i f f' j) (T : (modulePullbackDerived f) ⊡ (modulePullbackDerived i))
    (hM : IsPseudoCoherent Y T.fst) (hK' : IsPseudoCoherent X' T.snd) :
    (modulePullbackDerived.pushoutSquareFunctor h.toCommSq).essImage T := sorry

end AlgebraicGeometry.AlgebraicSpace
