/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Lemma_71_15_2_Fiber
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import stacks_project.Chap76.Lemma_76_52_13_BoundedBelow

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Lemma 76.52.13: let `S` be a scheme. Let `X` be an algebraic space over `S` such that
the structure morphism `toBase X : X ⟶ S` is flat and locally of finite presentation. Let
`E` be a pseudo-coherent object of `D(𝒪_X)`. Then `E` is `S`-perfect if and only if `E` is
locally bounded below and, for every point `s` of `S`, the derived pullback
`(pullback (fiberι (toBase X) s)).obj E` in `D(𝒪_{X_s})` is locally bounded below. -/
@[stacks 0GFK]
theorem isPerfectRelativeTo_iff_locallyBoundedBelow_and_fiber
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Flat (toBase X)] [LocallyOfFinitePresentation (toBase X)]
    (E : ModuleDerived X) (hE : IsPseudoCoherent X E) :
    IsPerfectRelativeTo (toBase X) E ↔
      IsLocallyBoundedBelow E ∧
        ∀ s : S, IsLocallyBoundedBelow ((pullback (fiberι (toBase X) s)).obj E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
