module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.Model

universe u

@[expose] public section

namespace AlgebraicGeometry.Curve

/-- For every degree bound over an algebraically closed field, there is a smooth proper
projective genus-one curve over the Laurent series field with constant global functions
which acquires semistable reduction after a finite extension, while every such extension
has degree greater than the bound. -/
theorem genusOneSemistableReductionDegree_unbounded
    (k : Type u) [Field k] [IsAlgClosed k] (B : ℕ) :
    ∃ (C : SchemeOverField (LaurentSeries k)) (_ : Curve C) (_ : Smooth C.hom)
      (_ : Projective C.hom) (_ : IsProper C.hom)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
      SchemeOverField.genus C (AlgebraicGeometry.topologicalKrullDim_eq_one C) hΓ = 1 ∧
        (∃ (K' : Type u) (_ : Field K') (_ : Algebra (LaurentSeries k) K')
          (_ : Algebra (PowerSeries k) K')
          (_ : IsScalarTower (PowerSeries k) (LaurentSeries k) K')
          (_ : FiniteDimensional (LaurentSeries k) K'),
          Scheme.Hom.hasSemistableReductionAtMaximal (PowerSeries k) (LaurentSeries k) K'
            (FieldExtension.Over.baseChange (LaurentSeries k) K' C)) ∧
        ∀ (K' : Type u) [Field K'] [Algebra (LaurentSeries k) K']
          [Algebra (PowerSeries k) K']
          [IsScalarTower (PowerSeries k) (LaurentSeries k) K']
          [FiniteDimensional (LaurentSeries k) K'],
          Scheme.Hom.hasSemistableReductionAtMaximal (PowerSeries k) (LaurentSeries k) K'
              (FieldExtension.Over.baseChange (LaurentSeries k) K' C) →
            B < Module.finrank (LaurentSeries k) K' := sorry

end AlgebraicGeometry.Curve
