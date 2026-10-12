/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import stacks_project.Chap67.Definition_67_48_3_Normalization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 67.48.3: for a scheme `S` and a quasi-compact quasi-separated morphism
`f : X ⟶ Y` of algebraic spaces over `S`, the normalization of `Y` in `X` is the morphism
`ν = Hom.fromNormalization f : Hom.normalization f ⟶ Y` over `S`, where
`Hom.normalization f` is the relative spectrum of the integral closure of `𝒪_Y` in
`f_* 𝒪_X`. -/
@[stacks 0822] #check AlgebraicGeometry.AlgebraicSpace.Hom.normalization

/- The canonical map from the relative normalization to the target. -/
@[stacks 0822] #check AlgebraicGeometry.AlgebraicSpace.Hom.fromNormalization

/- The canonical map from the source into the relative normalization. -/
@[stacks 0822] #check AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization

/- The canonical maps through the relative normalization factor the original morphism. -/
@[stacks 0822] #check
  AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization_fromNormalization
