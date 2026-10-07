module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Lemma_76_7_14

/-!
The sheaf `Ω[f]` is taken from Lemma 76.7.14, which reconstructs relative differentials
without rebuilding the broken `Chap66.Lemma_66_4_2_Comparison` owner used by
`Definition_76_7_2_Differentials`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 76.7.15: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. If `f` is locally of finite presentation, then `Ω[f]` is a finitely presented
`𝒪_X`-module. -/
@[stacks 05ZF]
instance isFinitePresentation_relativeDifferentials_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyOfFinitePresentation f] :
    (relativeDifferentials f).IsFinitePresentation :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
