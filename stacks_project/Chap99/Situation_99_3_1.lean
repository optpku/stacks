module

import StacksCheckRecall
public import stacks_project.Chap99.«99_3_1_1»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Situation 99.3.1: let `S` be a scheme, let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`, and let `F`, `G` be quasi-coherent `𝒪_X`-modules.
For a scheme `T` over `B`, write `X_T = baseChangeSpace f σ.hom = X ×_B T`
and write `F_T = baseChangeModule f σ.hom F`,
`G_T = baseChangeModule f σ.hom G` for the pullbacks of `F` and `G` along
the projection `baseChangeProj : X_T ⟶ X`. The Hom functor
`Hom(F, G) : (SchemeOver B)ᵒᵖ ⥤ Sets` sends `T` to
`Hom_{𝒪_{X_T}}(F_T, G_T)`. -/
@[stacks 08JT] #check AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor
