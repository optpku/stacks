/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.ShortExact
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Local
public import ReasLib.RingTheory.Kaehler.AbsoluteTransitivity
public import ReasLib.RingTheory.Kaehler.Quotient

/-!
# Determinant Comparison for Square Polynomial Quotients

This module constructs the conormal basis and determinant comparison maps for a
quasi-finite quotient of an `n`-variable polynomial algebra by `n` displayed
relations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ShortComplex.ShortExact
open scoped KaehlerDifferential Module.Determinant TensorProduct

noncomputable section

universe u

namespace Algebra.PolynomialQuotientDifferentials

variable (A : Type u) [CommRing A] (n : ℕ)
variable (f : Fin n → MvPolynomial (Fin n) A)

/-- The naive presentation of a quasi-finite square polynomial quotient is a
relative global complete intersection presentation. -/
theorem naivePresentation_isRelativeGlobalCompleteIntersection
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] :
    Algebra.Presentation.IsRelativeGlobalCompleteIntersection
      (Algebra.Presentation.naive : Algebra.Presentation A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) (Fin n) (Fin n)) := sorry

/-- A quasi-finite square polynomial quotient is a relative global complete
intersection over its coefficient ring. -/
instance relativeGlobalCompleteIntersection
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] :
    Algebra.IsRelativeGlobalCompleteIntersection A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) := sorry

/-- The displayed relation classes are linearly independent in the conormal
module of a quasi-finite square polynomial quotient. -/
theorem conormalGenerators_linearIndependent
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] :
    LinearIndependent (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
      (fun i ↦ (Ideal.span (Set.range f)).toCotangent
        ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩) := sorry

/-- The displayed relation classes span the conormal module of a quasi-finite
square polynomial quotient. -/
theorem conormalGenerators_span
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] :
    Submodule.span (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
        (Set.range fun i ↦ (Ideal.span (Set.range f)).toCotangent
          ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩) = ⊤ := sorry

/-- The displayed relation classes form the canonical basis of the conormal
module of a quasi-finite square polynomial quotient. -/
noncomputable def conormalBasis
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] :
    Module.Basis (Fin n)
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent :=
  Module.Basis.mk (conormalGenerators_linearIndependent A n f)
    (conormalGenerators_span A n f).ge

/-- The conormal module of a quasi-finite square polynomial quotient is free. -/
instance conormalFree
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] :
    Module.Free (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent := sorry

/-- The conormal module of a quasi-finite square polynomial quotient is finite. -/
instance conormalFinite
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] :
    Module.Finite (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent := sorry

/-- Relative polynomial differentials remain finite after passage to the quotient. -/
instance relativePolynomialDifferentialsFinite :
    Module.Finite (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
      ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[MvPolynomial (Fin n) A]
        Ω[MvPolynomial (Fin n) A⁄A]) := sorry

/-- The conormal module and the relative polynomial differential module of a quasi-finite
square presentation have the same rank. -/
theorem conormal_finrank_eq
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] :
    Module.finrank (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
        (Ideal.span (Set.range f)).Cotangent =
      Module.finrank (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
        ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[MvPolynomial (Fin n) A]
          Ω[MvPolynomial (Fin n) A⁄A]) := sorry

/-- The absolute and relative conormal maps form the commuting square below the
absolute Kähler transitivity row. -/
theorem conormal_comm
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] :
        ModuleCat.ofHom
          (KaehlerDifferential.Quotient.conormalToQuotient (Ideal.span (Set.range f))) ≫
        (KaehlerDifferential.AbsoluteTransitivity.complex A
          (MvPolynomial (Fin n) A)
          (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))).g =
      ModuleCat.ofHom
        (KaehlerDifferential.Quotient.conormalToQuotient (Ideal.span (Set.range f))) := sorry

/-- The cokernel of the absolute conormal map is canonically the module of absolute
Kähler differentials of the quotient. -/
noncomputable def absoluteCotangentEquiv :
    (cokernel (ModuleCat.ofHom
        (@KaehlerDifferential.Quotient.conormalToQuotient ℤ (MvPolynomial (Fin n) A)
          inferInstance inferInstance inferInstance (Ideal.span (Set.range f)) :
          (Ideal.span (Set.range f)).Cotangent →ₗ[
            MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
            (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[
              MvPolynomial (Fin n) A] Ω[MvPolynomial (Fin n) A⁄ℤ])) :
      ModuleCat (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))) ≃ₗ[
      MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
        Ω[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))⁄ℤ] :=
  let hExact : Function.Exact
      (KaehlerDifferential.Quotient.conormalToQuotient (Ideal.span (Set.range f)))
      (KaehlerDifferential.mapBaseChange ℤ (MvPolynomial (Fin n) A)
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))) :=
    KaehlerDifferential.Quotient.conormalToQuotient_exact (Ideal.span (Set.range f))
  (ModuleCat.cokernelIsoRangeQuotient
      (ModuleCat.ofHom (KaehlerDifferential.Quotient.conormalToQuotient
        (Ideal.span (Set.range f))))).toLinearEquiv ≪≫ₗ
    (hExact.linearEquivOfSurjective
      (KaehlerDifferential.mapBaseChange_surjective ℤ (MvPolynomial (Fin n) A)
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
        Ideal.Quotient.mk_surjective))

/-- The canonical cokernel equivalence is induced by Kähler base change. -/
theorem absoluteCotangentEquiv_comp_π :
    (absoluteCotangentEquiv A n f).toLinearMap.comp
        (cokernel.π (ModuleCat.ofHom
          (KaehlerDifferential.Quotient.conormalToQuotient (Ideal.span (Set.range f))))).hom =
      KaehlerDifferential.mapBaseChange ℤ (MvPolynomial (Fin n) A)
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) := sorry

/-- The determinant comparison map from absolute differential forms of a
quasi-finite square polynomial quotient to base forms and the determinant of
its two-term conormal complex. -/
noncomputable def comparison
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))]
    (p : ℕ) :
    (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
        Ω[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))⁄ℤ]).exteriorPower p →ₗ[
      MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
      (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
          ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A] Ω[A⁄ℤ])).exteriorPower p ⊗[
        MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
        (det[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))](
            ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
              (Ideal.span (Set.range f)).Cotangent) →ₗ[
          MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
          det[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))](
            ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
              ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[
                MvPolynomial (Fin n) A] Ω[MvPolynomial (Fin n) A⁄A]))) :=
  (exteriorComparison
      (KaehlerDifferential.AbsoluteTransitivity.shortExact_mvPolynomial A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) n)
      (ModuleCat.ofHom (KaehlerDifferential.Quotient.conormalToQuotient
        (Ideal.span (Set.range f))))
      (ModuleCat.ofHom (KaehlerDifferential.Quotient.conormalToQuotient
        (Ideal.span (Set.range f))))
      (conormal_comm A n f) (conormal_finrank_eq A n f) p).comp
    (ModuleCat.exteriorPower.map
      (ModuleCat.ofHom (absoluteCotangentEquiv A n f).symm.toLinearMap) p).hom

/-- In degree zero, the comparison sends the exterior unit to the discriminant
of the two-term conormal complex. -/
theorem comparison_zero
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] :
    comparison A n f 0
        (ModuleCat.exteriorPower.oneLinear
          (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
            Ω[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))⁄ℤ]) 1) =
      ModuleCat.exteriorPower.oneLinear
          (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
            ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A] Ω[A⁄ℤ])) 1 ⊗ₜ[
        MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
        ModuleCat.twoTermDiscriminant
          (ModuleCat.ofHom (KaehlerDifferential.Quotient.conormalToQuotient
            (Ideal.span (Set.range f))))
          (conormal_finrank_eq A n f) := sorry

/-- The comparison maps commute with left exterior multiplication by absolute
forms pulled back from the coefficient ring. -/
theorem comparison_wedge
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))]
    (q p : ℕ)
    (ω : (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
      ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A] Ω[A⁄ℤ])).exteriorPower q)
    (η : (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
      Ω[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))⁄ℤ]).exteriorPower p) :
    comparison A n f (q + p)
        (ModuleCat.exteriorPower.mul
          (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
            Ω[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))⁄ℤ]) q p
          (ModuleCat.exteriorPower.map
              (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange ℤ A
                (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)))) q ω ⊗ₜ η)) =
      _root_.TensorProduct.map
          (ModuleCat.exteriorPower.mul
            (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
              ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A] Ω[A⁄ℤ])) q p).hom
          LinearMap.id
        ((_root_.TensorProduct.assoc (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
          ((ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
            ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A] Ω[A⁄ℤ])).exteriorPower q)
          ((ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
            ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A] Ω[A⁄ℤ])).exteriorPower p)
          (det[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))](
              ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
                (Ideal.span (Set.range f)).Cotangent) →ₗ[
            MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
            det[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))](
              ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
                ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[
                  MvPolynomial (Fin n) A] Ω[MvPolynomial (Fin n) A⁄A])))).symm
          (ω ⊗ₜ comparison A n f p η)) := sorry

/-- Composing the comparison with base change on absolute forms is tensor
multiplication by the discriminant of the two-term conormal complex. -/
theorem comparison_comp_baseChange
    [Algebra.QuasiFinite A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))]
    (p : ℕ) :
    (comparison A n f p).comp
        (ModuleCat.exteriorPower.map
          (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange ℤ A
            (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)))) p).hom =
      (TensorProduct.mk (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
        ((ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
          ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A] Ω[A⁄ℤ])).exteriorPower p)
        (det[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))](
            ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
              (Ideal.span (Set.range f)).Cotangent) →ₗ[
          MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
          det[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))](
            ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
              ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[
                MvPolynomial (Fin n) A] Ω[MvPolynomial (Fin n) A⁄A])))).flip
        (ModuleCat.twoTermDiscriminant
          (ModuleCat.ofHom (KaehlerDifferential.Quotient.conormalToQuotient
            (Ideal.span (Set.range f))))
          (conormal_finrank_eq A n f)) := sorry

end Algebra.PolynomialQuotientDifferentials
