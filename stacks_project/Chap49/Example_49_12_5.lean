/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.LocalizedPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.LocalizedPresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Example 49.12.5 -/
@[stacks 0BWI] #check
  (Algebra.LocalizedPresentation.Univariate.noetherDifferent_eq_span_pderiv :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
      [Algebra.FiniteType A B] [Algebra.QuasiFinite A B]
      (f h : MvPolynomial (Fin 1) A) (q : Localization.Away h →ₐ[A] B),
      Function.Surjective q →
      RingHom.ker q.toRingHom =
        Ideal.span
          {algebraMap (MvPolynomial (Fin 1) A) (Localization.Away h) f} →
      KaehlerDifferential.noetherDifferent A B =
        Ideal.span
          {q (algebraMap (MvPolynomial (Fin 1) A) (Localization.Away h)
            (MvPolynomial.pderiv 0 f))})

#check
  (Algebra.LocalizedPresentation.Univariate.fittingIdeal_eq_span_pderiv :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
      [Algebra.FiniteType A B] [Algebra.QuasiFinite A B]
      (f h : MvPolynomial (Fin 1) A) (q : Localization.Away h →ₐ[A] B),
      Function.Surjective q →
      RingHom.ker q.toRingHom =
        Ideal.span
          {algebraMap (MvPolynomial (Fin 1) A) (Localization.Away h) f} →
      fittingIdeal B (KaehlerDifferential A B) 0 =
        Ideal.span
          {q (algebraMap (MvPolynomial (Fin 1) A) (Localization.Away h)
            (MvPolynomial.pderiv 0 f))})

#check
  (AlgebraicGeometry.Scheme.Hom.kaehlerDifferent_specMap_eq_idealSheaf_pderiv :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
      [Algebra.FiniteType A B] [Algebra.QuasiFinite A B]
      (f h : MvPolynomial (Fin 1) A) (q : Localization.Away h →ₐ[A] B),
      Function.Surjective q →
      RingHom.ker q.toRingHom =
        Ideal.span
          {algebraMap (MvPolynomial (Fin 1) A) (Localization.Away h) f} →
      @Scheme.Hom.kaehlerDifferent _ _
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          (HasRingHomProperty.Spec_iff.mpr
            (RingHom.finiteType_algebraMap.mpr inferInstance)) =
        Scheme.idealSheafDataOfIdealOnSpec
          (Ideal.span
            {q (algebraMap (MvPolynomial (Fin 1) A) (Localization.Away h)
              (MvPolynomial.pderiv 0 f))}))
