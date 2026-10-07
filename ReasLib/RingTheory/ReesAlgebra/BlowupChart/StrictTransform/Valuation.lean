module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.BaseChange
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.StrictTransform
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Valuation

/-!
# Valuation flattening by strict transforms

This leaf supplies the canonical source-chart actions on a base-changed strict transform and the
valuation-theoretic flattening statement.

@stack 053I
-/

@[expose] public section

open scoped AffineBlowupChart

noncomputable section

universe u v w x

namespace AffineBlowupChart.BaseChange

/-- The target affine blowup chart is canonically an algebra over the source chart. -/
@[stacks 053I "source-chart algebra structure on the target chart"]
instance instAlgebraSourceChartTarget
    {R : Type u} [CommRing R]
    {S : Type w} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) :
    Algebra R[I / a] (Target (S := S) I a) :=
  (map (S := S) I a).toRingHom.toAlgebra

/-- The strict transform over the base-changed chart carries the canonical source-chart module
structure by restriction along the chart comparison map. -/
@[stacks 053I "source-chart module structure on the strict transform"]
instance instModuleSourceChartStrictTransform
    {R : Type u} [CommRing R]
    {S : Type w} [CommRing S] [Algebra R S]
    {M : Type x} [AddCommGroup M] [Module S M]
    (I : Ideal R) (a : I) :
    Module R[I / a]
      (AffineBlowupChart.strictTransform
        (Ideal.map (algebraMap R S) I) (element I a) M) :=
  Module.compHom _ (algebraMap R[I / a] (Target (S := S) I a))

end AffineBlowupChart.BaseChange

namespace AffineBlowupChart.Valuation

/-- Lemma 15.26.2: for every valuation subring of the fraction field dominating a local domain,
some affine blowup approximation makes the strict-transform algebra flat and finitely presented
over the source chart, and makes the strict-transform module flat over the source chart and
finitely presented over that algebra. -/
@[stacks 053I "Lemma 15.26.2"]
theorem existsFlatFinitelyPresentedStrictTransforms
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {S : Type w} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    {M : Type x} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring) :
    ∃ (I : Ideal R) (a : AffineBlowupChart.NonzeroParameter I),
      let R' := R[I / a.1]
      let J : Ideal S := Ideal.map (algebraMap R S) I
      let b : J := AffineBlowupChart.BaseChange.element I a.1
      let B := S[J / b]
      let T := AffineBlowupChart.strictTransform J b M
      AffineBlowupChart.Valuation.IsApproximation A I a ∧
        Module.Flat R' B ∧
        Algebra.FinitePresentation R' B ∧
        Module.Flat R' T ∧
        Module.FinitePresentation B T := sorry

end AffineBlowupChart.Valuation
