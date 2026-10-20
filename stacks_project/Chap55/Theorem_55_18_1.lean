module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.Existence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

/- Theorem 55.18.1
A smooth projective curve over a DVR fraction field with only constant global functions
acquires semistable reduction after a finite separable extension. The following checks also
record the quadratic genus-zero model, the genus-one minimal-model classification, and the
uniform higher-genus degree bound.
-/
@[stacks 0CDN] #check (AlgebraicGeometry.Curve.existsSemistableReductionAfterFiniteSeparableExtension :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      Scheme.Hom.hasSemistableReductionAtMaximal R K K'
        (FieldExtension.Over.baseChange K K' C))

#check (AlgebraicGeometry.Curve.semistableReduction_genusZero :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections = 0),
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      Module.finrank K K' = 2 ∧
        Nonempty (FieldExtension.Over.baseChange K K' C ≅ ProjectiveSpace.schemeOver K' 1) ∧
        (let model := ProjectiveSpace.schemeOver (integralClosure R K') 1
         Smooth model.hom ∧ Projective model.hom ∧
           Nonempty (FieldExtension.Over.baseChange K K' C ≅
             Over.mk (pullback.snd model.hom
               (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R K') K')))))) ∧
        Scheme.Hom.hasSemistableReductionAtMaximal R K K'
          (FieldExtension.Over.baseChange K K' C))

#check (AlgebraicGeometry.Curve.semistableReduction_genusOne :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections = 1),
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      ∀ m : MaximalSpectrum (integralClosure R K'),
        ∃ branch : SemistableReductionBranch R K K'
            (FieldExtension.Over.baseChange K K' C) m,
          SemistableReductionBranch.genusOneShape m branch ∧
            SemistableReductionBranch.allMinimalModelsHaveGenusOneShape m branch)

#check (AlgebraicGeometry.Curve.semistableReduction_genusGeTwo :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus : g = SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections)
    (h_g : 2 ≤ g),
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      Scheme.Hom.hasSemistableReductionAtMaximal R K K'
          (FieldExtension.Over.baseChange K K' C) ∧
        Module.finrank K K' ≤ semistableReductionBound g)
