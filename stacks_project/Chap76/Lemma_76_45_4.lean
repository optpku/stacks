/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_5
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap76.Lemma_76_45_4_Relative

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Lemma 76.45.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `E` in `D_QCoh(𝒪_X)`. If `f` is flat and locally of finite
presentation, then `E` is pseudo-coherent relative to `Y` if and only if `E` is
pseudo-coherent on `X`. -/
@[stacks 0DII]
theorem isPseudoCoherentOver_iff_isPseudoCoherent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E) :
    IsPseudoCoherentOver f E ↔ IsPseudoCoherent X E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
