/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Curve.CyclicCover
public import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.UnboundedDegree

universe u

namespace AlgebraicGeometry.Curve

/- Example 55.16.1: for every degree bound over an algebraically closed field, there is a
smooth proper projective genus-one curve over `LaurentSeries k` which acquires semistable
reduction after a finite extension, while every such extension has degree above the bound.
The source constructs these curves as cyclic covers from order-`n` invertible modules; their
special-fibre multiplicity forces ramification index, and hence extension degree, at least `n`. -/
@[stacks 0CEH]
#check (AlgebraicGeometry.Curve.genusOneSemistableReductionDegree_unbounded :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : ℕ),
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
            B < Module.finrank (LaurentSeries k) K')

end AlgebraicGeometry.Curve
