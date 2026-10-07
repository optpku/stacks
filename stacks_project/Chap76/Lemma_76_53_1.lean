module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap70.Lemma_70_14_4_Pullback
public import stacks_project.Chap76.Lemma_76_53_1_DescentLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 76.53.1: Let `S` be a scheme and let `f : X ⟶ Y` be a flat proper
morphism of finite presentation of algebraic spaces over `S`. Let `E` be a
finite locally free `𝒪_X`-module. Assume that `𝒪_{Y'} ⟶ f'_* 𝒪_{X'}` is an
isomorphism for every base change `g : Y' ⟶ Y`. Then there exists an immersion
`j : Z ⟶ Y` of finite presentation such that `g` factors through `Z` if and
only if `(g')^* E` is the pullback of some finite locally free `𝒪_{Y'}`-module. -/
@[stacks 0D23]
theorem existsDescentLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [Proper f] [FinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (h_unit : ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
      IsIso (unitToPushforwardObjUnit (pullback.snd f g))) :
    ∃ (Z : AlgebraicSpace S) (j : Z ⟶ Y) (_ : IsImmersion j)
      (_ : FinitePresentation j), RepresentsDescentLocus f E j :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
