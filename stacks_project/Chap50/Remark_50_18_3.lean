module

import StacksCheckRecall
import ReasLib.RingTheory.Kaehler.PolynomialQuotient.DeterminantComparison

open CategoryTheory
open scoped KaehlerDifferential Module.Determinant TensorProduct

noncomputable section

universe u

/- Remark 50.18.3: for a quasi-finite square polynomial quotient, the canonical
maps from absolute differential forms to base forms tensored with the determinant
of the naive cotangent complex. -/
@[stacks 0FL9] #check
  (Algebra.PolynomialQuotientDifferentials.comparison :
    (A : Type u) → [CommRing A] → (n : ℕ) →
      (f : Fin n → MvPolynomial (Fin n) A) →
      [Algebra.QuasiFinite A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] →
      (p : ℕ) →
      (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
          Ω[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))⁄ℤ]).exteriorPower p →ₗ[
        MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
        (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
            ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A]
              Ω[A⁄ℤ])).exteriorPower p ⊗[
          MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
          (det[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))](
              ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
                (Ideal.span (Set.range f)).Cotangent) →ₗ[
            MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
            det[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))](
              ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
                ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[
                  MvPolynomial (Fin n) A] Ω[MvPolynomial (Fin n) A⁄A]))))

/- Remark 50.18.3: a quasi-finite square polynomial quotient is a relative
global complete intersection over its coefficient ring. -/
@[stacks 0FL9]
#check
  (Algebra.PolynomialQuotientDifferentials.relativeGlobalCompleteIntersection :
    (A : Type u) → [CommRing A] → (n : ℕ) →
      (f : Fin n → MvPolynomial (Fin n) A) →
      [Algebra.QuasiFinite A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] →
      Algebra.IsRelativeGlobalCompleteIntersection A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)))

/- Remark 50.18.3: the displayed relation classes form a basis of the conormal
module of the square presentation. -/
@[stacks 0FL9]
#check
  (Algebra.PolynomialQuotientDifferentials.conormalBasis :
    (A : Type u) → [CommRing A] → (n : ℕ) →
      (f : Fin n → MvPolynomial (Fin n) A) →
      [Algebra.QuasiFinite A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] →
      Module.Basis (Fin n)
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
        (Ideal.span (Set.range f)).Cotangent)

/- Remark 50.18.3: the displayed relation classes are linearly independent in
the conormal module of the square presentation. -/
@[stacks 0FL9]
#check
  (Algebra.PolynomialQuotientDifferentials.conormalGenerators_linearIndependent :
    (A : Type u) → [CommRing A] → (n : ℕ) →
      (f : Fin n → MvPolynomial (Fin n) A) →
      [Algebra.QuasiFinite A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] →
      LinearIndependent (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
        (fun i ↦ (Ideal.span (Set.range f)).toCotangent
          ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩))

/- Remark 50.18.3: the displayed relation classes span the conormal module of
the square presentation. -/
@[stacks 0FL9]
#check
  (Algebra.PolynomialQuotientDifferentials.conormalGenerators_span :
    (A : Type u) → [CommRing A] → (n : ℕ) →
      (f : Fin n → MvPolynomial (Fin n) A) →
      [Algebra.QuasiFinite A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] →
      Submodule.span (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
          (Set.range fun i ↦ (Ideal.span (Set.range f)).toCotangent
            ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩) = ⊤)

/- Remark 50.18.3: in degree zero, the comparison sends the exterior unit to
the discriminant of the two-term conormal complex. -/
@[stacks 0FL9]
#check
  (Algebra.PolynomialQuotientDifferentials.comparison_zero :
    (A : Type u) → [CommRing A] → (n : ℕ) →
      (f : Fin n → MvPolynomial (Fin n) A) →
      [Algebra.QuasiFinite A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] →
      Algebra.PolynomialQuotientDifferentials.comparison A n f 0
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
            (Algebra.PolynomialQuotientDifferentials.conormal_finrank_eq A n f))

/- Remark 50.18.3: the comparison maps commute with left exterior
multiplication by absolute forms pulled back from the coefficient ring. -/
@[stacks 0FL9]
#check
  (Algebra.PolynomialQuotientDifferentials.comparison_wedge :
    (A : Type u) → [CommRing A] → (n : ℕ) →
      (f : Fin n → MvPolynomial (Fin n) A) →
      [Algebra.QuasiFinite A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] →
      (q p : ℕ) →
      (ω : (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
        ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A] Ω[A⁄ℤ])).exteriorPower q) →
      (η : (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
        Ω[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))⁄ℤ]).exteriorPower p) →
      Algebra.PolynomialQuotientDifferentials.comparison A n f (q + p)
          (ModuleCat.exteriorPower.mul
            (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
              Ω[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))⁄ℤ]) q p
            (ModuleCat.exteriorPower.map
                (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange ℤ A
                  (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)))) q ω ⊗ₜ η)) =
        _root_.TensorProduct.map
            (ModuleCat.exteriorPower.mul
              (ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
                ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A]
                  Ω[A⁄ℤ])) q p).hom
            LinearMap.id
          ((_root_.TensorProduct.assoc (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
            ((ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
              ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A]
                Ω[A⁄ℤ])).exteriorPower q)
            ((ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
              ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[A]
                Ω[A⁄ℤ])).exteriorPower p)
            (det[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))](
                ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
                  (Ideal.span (Set.range f)).Cotangent) →ₗ[
              MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)]
              det[(MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))](
                ModuleCat.of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
                  ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) ⊗[
                    MvPolynomial (Fin n) A] Ω[MvPolynomial (Fin n) A⁄A])))).symm
            (ω ⊗ₜ Algebra.PolynomialQuotientDifferentials.comparison A n f p η)))

/- Remark 50.18.3: composing the comparison with base change on absolute forms
is tensor multiplication by the discriminant of the two-term conormal complex. -/
@[stacks 0FL9]
#check
  (Algebra.PolynomialQuotientDifferentials.comparison_comp_baseChange :
    (A : Type u) → [CommRing A] → (n : ℕ) →
      (f : Fin n → MvPolynomial (Fin n) A) →
      [Algebra.QuasiFinite A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))] →
      (p : ℕ) →
      (Algebra.PolynomialQuotientDifferentials.comparison A n f p).comp
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
            (Algebra.PolynomialQuotientDifferentials.conormal_finrank_eq A n f)))
