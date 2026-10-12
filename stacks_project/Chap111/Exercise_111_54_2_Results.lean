/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.NoetherNormalization
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.FunctionFieldEquivalence
public import ReasLib.RingTheory.Smooth.AtPrime.Jacobian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Algebra.Presentation
open IsRelativeGlobalCompleteIntersection.Jacobian

universe u

/- Exercise 111.54.2 (Results) (1): the valuative criterion of properness. -/
@[stacks 06A1] #check
  (AlgebraicGeometry.IsProper.eq_valuativeCriterion :
    @AlgebraicGeometry.IsProper =
      AlgebraicGeometry.ValuativeCriterion ⊓
        @AlgebraicGeometry.QuasiCompact ⊓
          @AlgebraicGeometry.QuasiSeparated ⊓
            @AlgebraicGeometry.LocallyOfFiniteType)

namespace AlgebraicGeometry.SchemeOverField

/-- Exercise 111.54.2 (Results) (2): for a variety `X` over a field `k`, the dimension of `X`
equals the transcendence degree of the function field of `X` over `k`. -/
@[stacks 06A1]
theorem topologicalKrullDim_eq_trdeg_functionField
    {k : Type u} [Field k] (X : SchemeOverField k) [Variety X] :
    topologicalKrullDim X.left =
      (Cardinal.toNat (Algebra.trdeg k (functionFieldCommAlg X)) : WithBot ℕ∞) := sorry

end AlgebraicGeometry.SchemeOverField

/- Exercise 111.54.2 (Results) (3): the category of nonsingular projective curves over `k` and
nonconstant morphisms is anti-equivalent to finitely generated field extensions of `k` of
transcendence degree one. -/
@[stacks 06A1] #check
  (AlgebraicGeometry.CurveCategory.oneVariableFunctionFieldsEquivNonsingularProjectiveCurves :
    ∀ (k : Type u) [Field k],
      Nonempty
        ((AlgebraicGeometry.FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
          AlgebraicGeometry.CurveCategory.NonsingularProjective k))

/- Exercise 111.54.2 (Results) (4): Noether normalization. -/
@[stacks 06A1] #check
  (exists_integral_inj_algHom_of_fg :
    ∀ (k : Type u) (R : Type u) [Field k] [CommRing R] [Nontrivial R]
      [Algebra k R] [Algebra.FiniteType k R],
      ∃ s, ∃ g : MvPolynomial (Fin s) k →ₐ[k] R,
        Function.Injective g ∧ g.IsIntegral)

/- Exercise 111.54.2 (Results) (5): Jacobian criterion. -/
@[stacks 06A1] #check @isSmoothAt_iff_exists_minor_not_mem
