module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap99.Lemma_99_12_1_Mor
public import stacks_project.Chap99.Proposition_99_12_3
public import stacks_project.Chap108.Lemma_108_5_2_Separated

/-!
# Lemma 108.10.2

The structure morphism of the functor of relative morphisms `Mor_B(Y, X)`
over `B` is separated and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- Lemma 108.10.2 (1): the structure morphism of Mor_B(Y, X) ⟶ B is
separated. -/
@[stacks 0DPN]
instance instIsSeparatedOver (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x] :
    Quot.IsSeparatedOver (mor y x) :=
  sorry

/-- Lemma 108.10.2 (2): the structure morphism of Mor_B(Y, X) ⟶ B is
locally of finite presentation. -/
@[stacks 0DPN]
theorem isLocallyOfFinitePresentationOver (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x] :
    IsLocallyOfFinitePresentationOver (mor y x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
