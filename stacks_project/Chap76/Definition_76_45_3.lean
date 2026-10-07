module

public import stacks_project.Chap76.Definition_76_45_3_Relative
public import stacks_project.Chap76.Definition_76_45_3_Module
import StacksCheckRecall

@[expose] public section

/- Definition 76.45.3 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. Let `E` be an object
of `D_QCoh(𝒪_X)`. Fix `m : ℤ`. We say `E` is `m`-pseudo-coherent relative to `Y`
if the equivalent conditions of Lemma 76.45.2 are satisfied. -/
@[stacks 0CSY] #check AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsMPseudoCoherentOver

/- Definition 76.45.3 (2): We say `E` is pseudo-coherent relative to `Y` if `E`
is `m`-pseudo-coherent relative to `Y` for all `m : ℤ`. -/
@[stacks 0CSY] #check AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPseudoCoherentOver

/- Definition 76.45.3 (3): Let `F` be a quasi-coherent `𝒪_X`-module. We say `F`
is `m`-pseudo-coherent relative to `Y` if `F` viewed as an object of
`D_QCoh(𝒪_X)` is `m`-pseudo-coherent relative to `Y`. -/
@[stacks 0CSY] #check AlgebraicGeometry.AlgebraicSpace.Modules.IsMPseudoCoherentOver

/- Definition 76.45.3 (4): We say `F` is pseudo-coherent relative to `Y` if `F`
viewed as an object of `D_QCoh(𝒪_X)` is pseudo-coherent relative to `Y`. -/
@[stacks 0CSY] #check AlgebraicGeometry.AlgebraicSpace.Modules.IsPseudoCoherentOver
