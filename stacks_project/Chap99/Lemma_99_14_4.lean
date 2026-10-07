module

public import stacks_project.Chap99.Lemma_99_14_4_BaseChange
public import stacks_project.Chap99.Lemma_99_14_4_SpaceOver

/-!
# Lemma 99.14.4

The groupoid of polarized proper algebraic-space families over an algebraic
space `T` over `Spec ℤ` is equivalent to the category of based functors from
the associated stack `S_T` to Polarized.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Polarized

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Lemma 99.14.4: for an algebraic space `T` over `Spec ℤ`, the groupoid of
pairs `(X ⟶ T, L)` with `X ⟶ T` a proper flat finitely presented morphism of
algebraic spaces and `L` relatively ample on `X / T` is equivalent to
`Mor` in `Cat / (Sch / Spec ℤ)_fppf` from the associated stack
`S_T = T.toGroupoids` to Polarized. The forward functor is base change of `X`
and restriction of `L` along scheme-points of `T`. -/
@[stacks 0E94]
instance SpaceOver.yoneda.instIsEquivalence (T : AlgebraicSpace specZ) :
    (SpaceOver.yoneda T).IsEquivalence :=
  sorry

end AlgebraicGeometry.Polarized
