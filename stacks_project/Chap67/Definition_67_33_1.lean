module

public import stacks_project.Chap67.Definition_67_33_1_FiberStalkDimension
public import stacks_project.Chap67.Definition_67_33_1_ResidueFieldTrdeg
public import stacks_project.Chap67.Definition_67_33_1_RelativeDimension
import StacksCheckRecall

@[expose] public section

/- Definition 67.33.1 (1): let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, let `x` be a point of `|X|`, and let `d : ℕ∞`. The
dimension of the local ring of the fibre of `f` at `x` is `d` if the equivalent
conditions of Lemma 67.22.5 hold for `fiberStalkKrullDimEq d`. -/
@[stacks 04NM] #check AlgebraicGeometry.AlgebraicSpace.FiberStalkDimEqAt

/- Definition 67.33.1 (2): let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, let `x` be a point of `|X|`, and let `r : ℕ∞`. The
transcendence degree of `x / f(x)` is `r` if the equivalent conditions of
Lemma 67.22.5 hold for `residueFieldTrdegEq r`. -/
@[stacks 04NM] #check AlgebraicGeometry.AlgebraicSpace.ResidueFieldTrdegEqAt

/- Definition 67.33.1 (3): let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, let `x` be a point of `|X|`, and let `d : ℕ∞`. The
morphism `f` has relative dimension `d` at `x` if the equivalent conditions of
Lemma 67.22.5 hold for the property that `dim_u(U_v)` equals `d`. -/
@[stacks 04NM] #check AlgebraicGeometry.AlgebraicSpace.RelativeDimensionAt
