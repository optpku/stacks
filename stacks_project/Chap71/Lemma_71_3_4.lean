module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_33_1_FiberStalkDimension
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.3.4

If a morphism of algebraic spaces is flat at a point whose fibre local ring has
dimension zero, then weakly associated points of a quasi-coherent module pull
back along that morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 71.3.4: for a scheme `S`, a morphism `f : X ⟶ Y` of algebraic spaces
over `S`, a quasi-coherent `𝒪_Y`-module `𝒢`, and a point `x` of `X`, if
`Points.map f x` is weakly associated to `𝒢`, `f` is flat at `x`, and the
dimension of the local ring of the fibre of `f` at `x` is zero, then `x` is
weakly associated to `(pullback f).obj 𝒢`. -/
@[stacks 0CUA]
theorem mem_weakAss_pullback_of_flatAt_of_fiberStalkDimEqAt_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (𝒢 : Y.Modules)
    [𝒢.IsQuasicoherent] (x : Points X) (hflat : FlatAt f x)
    (hdim : FiberStalkDimEqAt f 0 x) (hy : Points.map f x ∈ 𝒢.weakAss) :
    x ∈ ((pullback f).obj 𝒢).weakAss :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
