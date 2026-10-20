module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
public import ReasLib.RingTheory.FittingIdeal.BaseChange
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite
public import ReasLib.RingTheory.Ideal.Principal
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Localization

/-!
# Strict transforms on affine blowup charts

The strict transform is the quotient of the base-changed module by the primary component of the
distinguished chart parameter.  This leaf also owns its Fitting-ideal and local-freeness API.

@stack 053H
@stack 0CZM
@stack 0CZN
@stack 0BBJ
-/

@[expose] public section

open scoped AffineBlowupChart FittingIdeal PrimeSpectrum TensorProduct

noncomputable section

universe u v

namespace AffineBlowupChart

/-- Definition 15.26.1: the strict transform of an `R`-module `M` on the affine blowup chart
`R[I / a]` is the quotient of `R[I / a] ⊗[R] M` by the power-torsion primary component of the
image of `a`. -/
@[stacks 053H "Definition 15.26.1"]
abbrev strictTransform
    {R : Type u} [CommRing R] (I : Ideal R) (a : I)
    (M : Type v) [AddCommGroup M] [Module R M] : Type (max u v) :=
  let A := R[I / a]
  -- Local instance justification (defeq pin): keep the tensor-product action aligned with the
  -- named affine-chart algebra used by the distinguished parameter below.
  letI : Algebra R A := AffineBlowupChart.instAlgebra I a
  -- Local instance justification (defeq pin): expose the module structure carried by the pinned
  -- chart algebra to the tensor-product constructor.
  letI : Module R A := Algebra.toModule
  let T := A ⊗[R] M
  -- Local instance justification (defeq pin): make the quotient and primary component use the
  -- additive-group view of the tensor product rather than its parallel additive-monoid view.
  letI : AddCommGroup T :=
    TensorProduct.addCommGroup (R := R) (M := A) (N := M)
  let J : Ideal A := principalIdeal (AffineBlowupChart.algebraMap I a a)
  T ⧸ J.primaryComponent T

/-- The strict transform inherits its additive group from the quotient module. -/
@[stacks 053H "additive group on the strict transform", instance]
instance instAddCommGroupStrictTransform
    {R : Type u} [CommRing R] (I : Ideal R) (a : I)
    (M : Type v) [AddCommGroup M] [Module R M] :
    AddCommGroup (strictTransform I a M) := inferInstance

/-- The strict transform is canonically a module over its affine blowup chart. -/
@[stacks 053H "affine-chart module structure on the strict transform", instance]
instance instModuleStrictTransform
    {R : Type u} [CommRing R] (I : Ideal R) (a : I)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module R[I / a] (strictTransform I a M) := inferInstance

/-- Restriction along the affine-chart algebra map makes the strict transform an `R`-module. -/
@[stacks 053H "base-ring module structure on the strict transform", instance]
instance instModuleBaseStrictTransform
    {R : Type u} [CommRing R] (I : Ideal R) (a : I)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module R (strictTransform I a M) :=
  Module.compHom (strictTransform I a M) (algebraMap R R[I / a])

namespace StrictTransform

/-- Lemma 15.26.3: on the chart attached to an element of `Fit[R]_(k)(M)`, the `k`th Fitting
ideal of the strict transform is the unit ideal. -/
@[stacks 0CZM "Lemma 15.26.3"]
theorem fittingIdeal_eq_top
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (k : ℕ) (a : Fit[R]_(k)(M)) :
    let A := R[Fit[R]_(k)(M) / a]
    let M' := AffineBlowupChart.strictTransform (Fit[R]_(k)(M)) a M
    Fit[A]_(k)(M') = ⊤ := sorry

/-- Lemma 15.26.4: if `M` is free of rank `k` at every prime away from
`V(Fit[R]_(k)(M))`, then every corresponding affine-chart strict transform is finite locally
free of rank `k`. -/
@[stacks 0CZN "Lemma 15.26.4"]
theorem finiteLocallyFreeOfRank
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (k : ℕ) (a : Fit[R]_(k)(M))
    (hM :
      ∀ (p : Ideal R) [p.IsPrime] (_ : ¬ Fit[R]_(k)(M) ≤ p),
        Nonempty
          ((LocalizedModule.AtPrime p M) ≃ₗ[Localization.AtPrime p]
            (Fin k → Localization.AtPrime p))) :
    Module.FiniteLocallyFreeOfRank R[Fit[R]_(k)(M) / a]
      (AffineBlowupChart.strictTransform (Fit[R]_(k)(M)) a M) k := sorry

/-- Lemma 15.26.5: if `M` is finite and becomes finite locally free of rank `r` after inverting
`f`, then a finitely generated ideal with the same vanishing locus as `f` makes every affine-chart
strict transform finite locally free of rank `r`. -/
@[stacks 0BBJ "Lemma 15.26.5"]
theorem existsCenterFiniteLocallyFreeOfRank
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (f : R) (r : ℕ)
    (hMf : Module.FiniteLocallyFreeOfRank
      (Localization.Away f) (LocalizedModule.Away f M) r) :
    ∃ I : Ideal R,
      I.FG ∧
      V(({f} : Set R)) = V((I : Set R)) ∧
      ∀ a : I, Module.FiniteLocallyFreeOfRank R[I / a]
        (AffineBlowupChart.strictTransform I a M) r := sorry

end StrictTransform

end AffineBlowupChart
