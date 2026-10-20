/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.FunctionFieldEquivalence

@[expose] public section

open CategoryTheory

universe u

open AlgebraicGeometry

/- Theorem 53.2.6 (1): finitely generated extensions of `k` of transcendence degree one,
with arrows reversed, are canonically equivalent to curves over `k` with dominant rational
maps. -/
@[stacks 0BY1] #check
  (AlgebraicGeometry.CurveCategory.dominantRationalMapFunctionFieldFunctor_isEquivalence :
    ∀ {k : Type u} [Field k],
      (AlgebraicGeometry.CurveCategory.dominantRationalMapFunctionFieldFunctor (k := k)).IsEquivalence)

/- Theorem 53.2.6 (2): finitely generated extensions of `k` of transcendence degree one,
with arrows reversed, are canonically equivalent to normal projective curves over `k` with
nonconstant morphisms. -/
@[stacks 0BY1] #check
  (AlgebraicGeometry.CurveCategory.normalProjectiveFunctionFieldFunctor_isEquivalence :
    ∀ {k : Type u} [Field k],
      (AlgebraicGeometry.CurveCategory.curveFunctionFieldFunctor
        (AlgebraicGeometry.CurveCategory.normalProjectiveProperty k) (fun X hX ↦ hX.1)).IsEquivalence)

/- Theorem 53.2.6 (3): finitely generated extensions of `k` of transcendence degree one,
with arrows reversed, are canonically equivalent to nonsingular projective curves over `k`
with nonconstant morphisms. -/
@[stacks 0BY1] #check
  (AlgebraicGeometry.CurveCategory.nonsingularProjectiveFunctionFieldFunctor_isEquivalence :
    ∀ {k : Type u} [Field k],
      (AlgebraicGeometry.CurveCategory.curveFunctionFieldFunctor
        (AlgebraicGeometry.CurveCategory.nonsingularProjectiveProperty k) (fun X hX ↦ hX.1)).IsEquivalence)

/- Theorem 53.2.6 (4): finitely generated extensions of `k` of transcendence degree one,
with arrows reversed, are canonically equivalent to regular projective curves over `k` with
nonconstant morphisms. -/
@[stacks 0BY1] #check
  (AlgebraicGeometry.CurveCategory.regularProjectiveFunctionFieldFunctor_isEquivalence :
    ∀ {k : Type u} [Field k],
      (AlgebraicGeometry.CurveCategory.curveFunctionFieldFunctor
        (AlgebraicGeometry.CurveCategory.regularProjectiveProperty k) (fun X hX ↦ hX.1)).IsEquivalence)

/- Theorem 53.2.6 (5): finitely generated extensions of `k` of transcendence degree one,
with arrows reversed, are canonically equivalent to normal proper curves over `k` with
nonconstant morphisms. -/
@[stacks 0BY1] #check
  (AlgebraicGeometry.CurveCategory.normalProperFunctionFieldFunctor_isEquivalence :
    ∀ {k : Type u} [Field k],
      (AlgebraicGeometry.CurveCategory.curveFunctionFieldFunctor
        (AlgebraicGeometry.CurveCategory.normalProperProperty k) (fun X hX ↦ hX.1)).IsEquivalence)
