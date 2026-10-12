/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.Yoneda
import StacksCheckRecall

/-!
# Lemma 99.14.4

The groupoid of polarized proper algebraic-space families over an algebraic
space `T` over `Spec ℤ` is equivalent to the category of based functors from
the associated stack `S_T` to Polarized.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 99.14.4: for an algebraic space `T` over `Spec ℤ`, the groupoid of
pairs `(X ⟶ T, L)` with `X ⟶ T` a proper flat finitely presented morphism of
algebraic spaces and `L` relatively ample on `X / T` is equivalent to
`Mor` in `Cat / (Sch / Spec ℤ)_fppf` from the associated stack `S_T` to
Polarized. The forward functor is base change of `X` and restriction of `L`
along scheme-points of `T`. -/
@[stacks 0E94] #check
  (AlgebraicGeometry.Polarized.SpaceOver.yoneda.instIsEquivalence :
    ∀ (T : AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Polarized.specZ.{u}),
      (AlgebraicGeometry.Polarized.SpaceOver.yoneda T).IsEquivalence)
