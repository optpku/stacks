/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin
public import stacks_project.Chap71.Lemma_71_4_6_Tensor
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Weakly associated points of a tensor with pullback at a flat point

For a locally finite-type morphism of algebraic spaces, a finite-type
quasi-coherent module that is flat at a point over the target, and a
quasi-coherent module on the target, membership of that point in the weakly
associated locus of the tensor with pullback is equivalent to the image
lying in the weakly associated locus of the base module together with
relative assassin membership.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 77.4.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. Let `x : Points X`
with image `y = Points.map f x`. Let `F` be a finite type quasi-coherent
`𝒪_X`-module, and let `G` be a quasi-coherent `𝒪_Y`-module. If `F` is flat
at `x` over `Y`, then `x ∈ (tensorPullback F f G).weakAss` if and only if
`y ∈ G.weakAss` and `x ∈ relativeAssassin f F`. Under locally of finite type,
`Ass_{X/Y}(F)` is `relativeAssassin f F`, and `tensorPullback F f G` is
`F ⊗ f^* G`. -/
@[stacks 0CVK]
theorem mem_weakAss_tensorPullback_iff_of_flatOverAt
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (G : Y.Modules) [G.IsQuasicoherent] (x : Points X)
    (h_flat : flatOverAt F f x) :
    x ∈ (tensorPullback F f G).weakAss ↔
      Points.map f x ∈ G.weakAss ∧ x ∈ relativeAssassin f F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
