/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.FinitePresentation.RestrictScalars
public import ReasLib.RingTheory.GenericFlatness.Localization.Intermediate
public import ReasLib.RingTheory.MvPolynomial.Localization.Module

/-!
# Multivariate Polynomial Models for Generic Flatness

This leaf specializes the intermediate-presentation generic-flatness API to
finite-variable coefficient-localized multivariate polynomial rings.  It
relies on Mathlib's finite-presentation instance for a finite-variable
polynomial algebra and on the reusable finite-presentation transport for a
compatible module over a finitely presented algebra.

@stack 051T
-/

@[expose] public section

universe u v w x

namespace GenericFlatness.LocalizationCondition

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

/-- Tag `051T`: the finite-variable multivariate-polynomial specialization of
`LocalizationCondition.ofIntermediate`.  The finite-presentation instance for
`R_f[x_i]` is supplied by Mathlib.  Finite presentation of both target
localizations as `R_f[x_i]`-modules, together with the compatible scalar
tower, is promoted to the target algebra/module finite-presentation data
required by the generic localization condition. -/
@[stacks 051T "generic-flatness polynomial localization condition"]
theorem ofMvPolynomial
    {σ : Type x} [Finite σ] (f : R)
    [Algebra (MvPolynomial σ (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [Module (MvPolynomial σ (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    (h_algebra_tower :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        Localization.Away.Relative.algebraMapAlgebra (R := R) (S := S) f
      IsScalarTower (Localization.Away f)
        (MvPolynomial σ (Localization.Away f))
        (Localization.Away (algebraMap R S f)))
    [IsScalarTower (MvPolynomial σ (Localization.Away f))
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    [Module.FinitePresentation (MvPolynomial σ (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [Module.FinitePresentation (MvPolynomial σ (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    (h_free_algebra :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        Localization.Away.Relative.algebraMapAlgebra (R := R) (S := S) f
      Module.Free (Localization.Away f) (Localization.Away (algebraMap R S f)))
    (h_free_module :
      letI : Module (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M) :=
        Localization.Away.Relative.algebraMapModule (R := R) (S := S) (M := M) f
      Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M)) :
    LocalizationCondition R S M f := sorry

/-- Tag `051T`: finitely presented polynomial source models whose coefficient-away
localizations are polynomial-linearly equivalent to the target algebra and module give the
generic-flatness localization condition.  The model actions are fixed to
`MvPolynomial.Localization.awayCModule` and `MvPolynomial.Localization.awayCBaseModule`; the
canonical relative `R_f`-action on the target module is supplied through
`Localization.Away.Relative.mapModule_isScalarTower_of_tower`. -/
@[stacks 051T "generic-flatness polynomial model localization condition"]
theorem ofMvPolynomialModels
    {σ : Type x} [Finite σ] (f : R)
    {S' : Type*} [AddCommGroup S'] [Module (MvPolynomial σ R) S']
    {M' : Type*} [AddCommGroup M'] [Module (MvPolynomial σ R) M']
    [Algebra (MvPolynomial σ (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [Module (MvPolynomial σ (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    (h_algebra_tower :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        Localization.Away.Relative.algebraMapAlgebra (R := R) (S := S) f
      IsScalarTower (Localization.Away f)
        (MvPolynomial σ (Localization.Away f))
        (Localization.Away (algebraMap R S f)))
    [IsScalarTower (MvPolynomial σ (Localization.Away f))
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    [Module.FinitePresentation (MvPolynomial σ R) S']
    [Module.FinitePresentation (MvPolynomial σ R) M']
    (h_free_S' :
      letI : Module (Localization.Away f)
          (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) S') :=
        MvPolynomial.Localization.awayCBaseModule (σ := σ) (N := S') f
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) S'))
    (h_free_M' :
      letI : Module (Localization.Away f)
          (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) M') :=
        MvPolynomial.Localization.awayCBaseModule (σ := σ) (N := M') f
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) M'))
    (eS :
      letI : Module (MvPolynomial σ (Localization.Away f))
          (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) S') :=
        MvPolynomial.Localization.awayCModule (σ := σ) (N := S') f
      LocalizedModule.Away (MvPolynomial.C (σ := σ) f) S' ≃ₗ[
        MvPolynomial σ (Localization.Away f)] Localization.Away (algebraMap R S f))
    (eM :
      letI : Module (MvPolynomial σ (Localization.Away f))
          (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) M') :=
        MvPolynomial.Localization.awayCModule (σ := σ) (N := M') f
      LocalizedModule.Away (MvPolynomial.C (σ := σ) f) M' ≃ₗ[
        MvPolynomial σ (Localization.Away f)]
          LocalizedModule.Away (algebraMap R S f) M) :
    LocalizationCondition R S M f := sorry

end GenericFlatness.LocalizationCondition
