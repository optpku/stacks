/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_13_4_BaseChange
public import stacks_project.Chap99.Lemma_99_13_4_Over

/-!
# Lemma 99.13.4

The groupoid of finite-type morphisms of algebraic spaces into an algebraic
space `T` is equivalent to the category of based functors from the associated
stack `S_T` to `Spaces'_ft`, and likewise for finite-presentation, flat, and
proper morphisms versus `Spaces'_{fp, flat, proper}`. The source states this
over `Spec ℤ`; the declarations are relative to a general base scheme `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Lemma 99.13.4 (1): for an algebraic space `T` over a scheme `S` (source:
over `Spec ℤ`), the groupoid of finite-type morphisms `X ⟶ T` of algebraic
spaces is equivalent to `Mor` in `Cat / (Sch/S)_fppf` from the associated stack
`S_T = T.toGroupoids` to `Spaces'_ft`. The forward functor is base change of
`X` along scheme-points of `T`. -/
@[stacks 0E93]
instance FtOver.yoneda.instIsEquivalence {S : Scheme.{u}} (T : AlgebraicSpace S) :
    (FtOver.yoneda T).IsEquivalence := sorry

/-- Lemma 99.13.4 (2): for an algebraic space `T` over a scheme `S` (source:
over `Spec ℤ`), the groupoid of finite-presentation, flat, and proper morphisms
`X ⟶ T` of algebraic spaces is equivalent to `Mor` in `Cat / (Sch/S)_fppf` from
the associated stack `S_T = T.toGroupoids` to `Spaces'_{fp, flat, proper}`. The
forward functor is base change of `X` along scheme-points of `T`. -/
@[stacks 0E93]
instance FpFlatProperOver.yoneda.instIsEquivalence {S : Scheme.{u}}
    (T : AlgebraicSpace S) : (FpFlatProperOver.yoneda T).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
