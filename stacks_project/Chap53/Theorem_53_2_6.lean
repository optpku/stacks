/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
@[stacks 0BY1] #check (AlgebraicGeometry.CurveCategory.oneVariableFunctionFieldsEquivCurveRationalMaps :
    ∀ (k : Type u) [Field k],
      Nonempty
        ((AlgebraicGeometry.FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
          AlgebraicGeometry.CurveCategory.DominantRationalMap k))

/- Theorem 53.2.6 (2): finitely generated extensions of `k` of transcendence degree one,
with arrows reversed, are canonically equivalent to normal projective curves over `k` with
nonconstant morphisms. -/
@[stacks 0BY1] #check (AlgebraicGeometry.CurveCategory.oneVariableFunctionFieldsEquivNormalProjectiveCurves :
    ∀ (k : Type u) [Field k],
      Nonempty
        ((AlgebraicGeometry.FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
          AlgebraicGeometry.CurveCategory.NormalProjective k))

/- Theorem 53.2.6 (3): finitely generated extensions of `k` of transcendence degree one,
with arrows reversed, are canonically equivalent to nonsingular projective curves over `k`
with nonconstant morphisms. -/
@[stacks 0BY1] #check (AlgebraicGeometry.CurveCategory.oneVariableFunctionFieldsEquivNonsingularProjectiveCurves :
    ∀ (k : Type u) [Field k],
      Nonempty
        ((AlgebraicGeometry.FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
          AlgebraicGeometry.CurveCategory.NonsingularProjective k))

/- Theorem 53.2.6 (4): finitely generated extensions of `k` of transcendence degree one,
with arrows reversed, are canonically equivalent to regular projective curves over `k` with
nonconstant morphisms. -/
@[stacks 0BY1] #check (AlgebraicGeometry.CurveCategory.oneVariableFunctionFieldsEquivRegularProjectiveCurves :
    ∀ (k : Type u) [Field k],
      Nonempty
        ((AlgebraicGeometry.FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
          AlgebraicGeometry.CurveCategory.RegularProjective k))

/- Theorem 53.2.6 (5): finitely generated extensions of `k` of transcendence degree one,
with arrows reversed, are canonically equivalent to normal proper curves over `k` with
nonconstant morphisms. -/
@[stacks 0BY1] #check (AlgebraicGeometry.CurveCategory.oneVariableFunctionFieldsEquivNormalProperCurves :
    ∀ (k : Type u) [Field k],
      Nonempty
        ((AlgebraicGeometry.FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
          AlgebraicGeometry.CurveCategory.NormalProper k))
