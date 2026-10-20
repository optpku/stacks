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

universe u v

/- Exercise 111.54.2 (Results) (2): for a variety `X` over a field `k`, the dimension of `X`
equals the transcendence degree of the function field of `X` over `k`. -/
@[stacks 06A1] #check
  (AlgebraicGeometry.SchemeOverField.topologicalKrullDim_eq_trdeg_functionField :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Variety X],
      topologicalKrullDim X.left =
        (Cardinal.toNat (Algebra.trdeg k
          (AlgebraicGeometry.SchemeOverField.functionFieldCommAlg X)) : WithBot ℕ∞))

/- Exercise 111.54.2 (Results) (1): the valuative criterion of properness. -/
@[stacks 06A1] #check
  (AlgebraicGeometry.IsProper.eq_valuativeCriterion :
    @AlgebraicGeometry.IsProper =
      AlgebraicGeometry.ValuativeCriterion ⊓
        @AlgebraicGeometry.QuasiCompact ⊓
          @AlgebraicGeometry.QuasiSeparated ⊓
            @AlgebraicGeometry.LocallyOfFiniteType)

/- Exercise 111.54.2 (Results) (3): the category of nonsingular projective curves over `k` and
nonconstant morphisms is anti-equivalent to finitely generated field extensions of `k` of
transcendence degree one. -/
@[stacks 06A1] #check
  (AlgebraicGeometry.CurveCategory.nonsingularProjectiveFunctionFieldFunctor_isEquivalence :
    ∀ {k : Type u} [Field k],
      (AlgebraicGeometry.CurveCategory.curveFunctionFieldFunctor
        (AlgebraicGeometry.CurveCategory.nonsingularProjectiveProperty k) (fun X hX ↦ hX.1)).IsEquivalence)

/- Exercise 111.54.2 (Results) (4): Noether normalization. -/
@[stacks 06A1] #check
  (exists_integral_inj_algHom_of_fg :
    ∀ (k : Type u) (R : Type u) [Field k] [CommRing R] [Nontrivial R]
      [Algebra k R] [Algebra.FiniteType k R],
      ∃ s, ∃ g : MvPolynomial (Fin s) k →ₐ[k] R,
        Function.Injective g ∧ g.IsIntegral)

/- Exercise 111.54.2 (Results) (5): Jacobian criterion. -/
@[stacks 06A1] #check
  (Algebra.Presentation.IsRelativeGlobalCompleteIntersection.Jacobian.isSmoothAt_iff_exists_minor_not_mem :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      {n c : ℕ} {P : Algebra.Presentation R S (Fin n) (Fin c)}
      (hP : P.IsRelativeGlobalCompleteIntersection) (q : PrimeSpectrum S),
      Algebra.IsSmoothAt R q.asIdeal ↔
        ∃ I : Set.powersetCard (Fin n) c,
          algebraMap P.Ring S
            (P.jacobianColumnMinor (Fin.castLEEmb le_rfl) I) ∉ q.asIdeal)
